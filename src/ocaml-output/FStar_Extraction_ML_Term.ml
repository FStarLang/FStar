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
      if FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid
      then FStar_Extraction_ML_Syntax.E_PURE
      else
        if FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GHOST_lid
        then FStar_Extraction_ML_Syntax.E_GHOST
        else
          (let ed_opt =
             FStar_TypeChecker_Env.effect_decl_opt
               g.FStar_Extraction_ML_UEnv.tcenv l1
              in
           match ed_opt with
           | FStar_Pervasives_Native.Some (ed,qualifiers) ->
               let uu____336 =
                 FStar_All.pipe_right qualifiers
                   (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                  in
               if uu____336
               then FStar_Extraction_ML_Syntax.E_PURE
               else FStar_Extraction_ML_Syntax.E_IMPURE
           | FStar_Pervasives_Native.None  ->
               FStar_Extraction_ML_Syntax.E_IMPURE)
  
let rec (is_arity :
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t  in
      let uu____353 =
        let uu____354 = FStar_Syntax_Subst.compress t1  in
        uu____354.FStar_Syntax_Syntax.n  in
      match uu____353 with
      | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____357 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_ascribed uu____382 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_meta uu____409 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____417 = FStar_Syntax_Util.unfold_lazy i  in
          is_arity env uu____417
      | FStar_Syntax_Syntax.Tm_uvar uu____418 -> false
      | FStar_Syntax_Syntax.Tm_constant uu____435 -> false
      | FStar_Syntax_Syntax.Tm_name uu____436 -> false
      | FStar_Syntax_Syntax.Tm_quoted uu____437 -> false
      | FStar_Syntax_Syntax.Tm_bvar uu____444 -> false
      | FStar_Syntax_Syntax.Tm_type uu____445 -> true
      | FStar_Syntax_Syntax.Tm_arrow (uu____446,c) ->
          is_arity env (FStar_Syntax_Util.comp_result c)
      | FStar_Syntax_Syntax.Tm_fvar uu____464 ->
          let t2 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Normalize.AllowUnboundUniverses;
              FStar_TypeChecker_Normalize.EraseUniverses;
              FStar_TypeChecker_Normalize.UnfoldUntil
                FStar_Syntax_Syntax.Delta_constant]
              env.FStar_Extraction_ML_UEnv.tcenv t1
             in
          let uu____466 =
            let uu____467 = FStar_Syntax_Subst.compress t2  in
            uu____467.FStar_Syntax_Syntax.n  in
          (match uu____466 with
           | FStar_Syntax_Syntax.Tm_fvar uu____470 -> false
           | uu____471 -> is_arity env t2)
      | FStar_Syntax_Syntax.Tm_app uu____472 ->
          let uu____487 = FStar_Syntax_Util.head_and_args t1  in
          (match uu____487 with | (head1,uu____503) -> is_arity env head1)
      | FStar_Syntax_Syntax.Tm_uinst (head1,uu____525) -> is_arity env head1
      | FStar_Syntax_Syntax.Tm_refine (x,uu____531) ->
          is_arity env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_abs (uu____536,body,uu____538) ->
          is_arity env body
      | FStar_Syntax_Syntax.Tm_let (uu____559,body) -> is_arity env body
      | FStar_Syntax_Syntax.Tm_match (uu____577,branches) ->
          (match branches with
           | (uu____615,uu____616,e)::uu____618 -> is_arity env e
           | uu____665 -> false)
  
let rec (is_type_aux :
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____689 ->
          let uu____714 =
            let uu____715 = FStar_Syntax_Print.tag_of_term t1  in
            FStar_Util.format1 "Impossible: %s" uu____715  in
          failwith uu____714
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____716 =
            let uu____717 = FStar_Syntax_Print.tag_of_term t1  in
            FStar_Util.format1 "Impossible: %s" uu____717  in
          failwith uu____716
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____719 = FStar_Syntax_Util.unfold_lazy i  in
          is_type_aux env uu____719
      | FStar_Syntax_Syntax.Tm_constant uu____720 -> false
      | FStar_Syntax_Syntax.Tm_type uu____721 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____722 -> true
      | FStar_Syntax_Syntax.Tm_arrow uu____729 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.failwith_lid ->
          false
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Extraction_ML_UEnv.is_type_name env fv
      | FStar_Syntax_Syntax.Tm_uvar (uu____744,t2) -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_bvar
          { FStar_Syntax_Syntax.ppname = uu____770;
            FStar_Syntax_Syntax.index = uu____771;
            FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_name
          { FStar_Syntax_Syntax.ppname = uu____775;
            FStar_Syntax_Syntax.index = uu____776;
            FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____781,uu____782) ->
          is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____824) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____831) ->
          let uu____852 = FStar_Syntax_Subst.open_term bs body  in
          (match uu____852 with | (uu____857,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
          let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
          let uu____874 =
            let uu____879 =
              let uu____880 = FStar_Syntax_Syntax.mk_binder x  in [uu____880]
               in
            FStar_Syntax_Subst.open_term uu____879 body  in
          (match uu____874 with | (uu____881,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_let ((uu____883,lbs),body) ->
          let uu____900 = FStar_Syntax_Subst.open_let_rec lbs body  in
          (match uu____900 with | (uu____907,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_match (uu____913,branches) ->
          (match branches with
           | b::uu____952 ->
               let uu____997 = FStar_Syntax_Subst.open_branch b  in
               (match uu____997 with
                | (uu____998,uu____999,e) -> is_type_aux env e)
           | uu____1017 -> false)
      | FStar_Syntax_Syntax.Tm_quoted uu____1034 -> false
      | FStar_Syntax_Syntax.Tm_meta (t2,uu____1042) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_app (head1,uu____1048) ->
          is_type_aux env head1
  
let (is_type :
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      FStar_Extraction_ML_UEnv.debug env
        (fun uu____1079  ->
           let uu____1080 = FStar_Syntax_Print.tag_of_term t  in
           let uu____1081 = FStar_Syntax_Print.term_to_string t  in
           FStar_Util.print2 "checking is_type (%s) %s\n" uu____1080
             uu____1081);
      (let b = is_type_aux env t  in
       FStar_Extraction_ML_UEnv.debug env
         (fun uu____1087  ->
            if b
            then
              let uu____1088 = FStar_Syntax_Print.term_to_string t  in
              let uu____1089 = FStar_Syntax_Print.tag_of_term t  in
              FStar_Util.print2 "is_type %s (%s)\n" uu____1088 uu____1089
            else
              (let uu____1091 = FStar_Syntax_Print.term_to_string t  in
               let uu____1092 = FStar_Syntax_Print.tag_of_term t  in
               FStar_Util.print2 "not a type %s (%s)\n" uu____1091 uu____1092));
       b)
  
let is_type_binder :
  'Auu____1096 .
    FStar_Extraction_ML_UEnv.env ->
      (FStar_Syntax_Syntax.bv,'Auu____1096) FStar_Pervasives_Native.tuple2 ->
        Prims.bool
  =
  fun env  ->
    fun x  ->
      is_arity env (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
  
let (is_constructor : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1116 =
      let uu____1117 = FStar_Syntax_Subst.compress t  in
      uu____1117.FStar_Syntax_Syntax.n  in
    match uu____1116 with
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____1120;
          FStar_Syntax_Syntax.fv_delta = uu____1121;
          FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
            (FStar_Syntax_Syntax.Data_ctor );_}
        -> true
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____1122;
          FStar_Syntax_Syntax.fv_delta = uu____1123;
          FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
            (FStar_Syntax_Syntax.Record_ctor uu____1124);_}
        -> true
    | uu____1131 -> false
  
let rec (is_fstar_value : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1135 =
      let uu____1136 = FStar_Syntax_Subst.compress t  in
      uu____1136.FStar_Syntax_Syntax.n  in
    match uu____1135 with
    | FStar_Syntax_Syntax.Tm_constant uu____1139 -> true
    | FStar_Syntax_Syntax.Tm_bvar uu____1140 -> true
    | FStar_Syntax_Syntax.Tm_fvar uu____1141 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____1142 -> true
    | FStar_Syntax_Syntax.Tm_app (head1,args) ->
        let uu____1181 = is_constructor head1  in
        if uu____1181
        then
          FStar_All.pipe_right args
            (FStar_List.for_all
               (fun uu____1197  ->
                  match uu____1197 with
                  | (te,uu____1203) -> is_fstar_value te))
        else false
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____1206) -> is_fstar_value t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____1212,uu____1213) ->
        is_fstar_value t1
    | uu____1254 -> false
  
let rec (is_ml_value : FStar_Extraction_ML_Syntax.mlexpr -> Prims.bool) =
  fun e  ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_Const uu____1258 -> true
    | FStar_Extraction_ML_Syntax.MLE_Var uu____1259 -> true
    | FStar_Extraction_ML_Syntax.MLE_Name uu____1260 -> true
    | FStar_Extraction_ML_Syntax.MLE_Fun uu____1261 -> true
    | FStar_Extraction_ML_Syntax.MLE_CTor (uu____1272,exps) ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Tuple exps ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Record (uu____1281,fields) ->
        FStar_Util.for_all
          (fun uu____1306  ->
             match uu____1306 with | (uu____1311,e1) -> is_ml_value e1)
          fields
    | FStar_Extraction_ML_Syntax.MLE_TApp (h,uu____1314) -> is_ml_value h
    | uu____1319 -> false
  
let (fresh : Prims.string -> Prims.string) =
  let c = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun x  ->
    FStar_Util.incr c;
    (let uu____1360 =
       let uu____1361 = FStar_ST.op_Bang c  in
       FStar_Util.string_of_int uu____1361  in
     Prims.strcat x uu____1360)
  
let (normalize_abs : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t0  ->
    let rec aux bs t copt =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_abs (bs',body,copt1) ->
          aux (FStar_List.append bs bs') body copt1
      | uu____1460 ->
          let e' = FStar_Syntax_Util.unascribe t1  in
          let uu____1462 = FStar_Syntax_Util.is_fun e'  in
          if uu____1462
          then aux bs e' copt
          else FStar_Syntax_Util.abs bs e' copt
       in
    aux [] t0 FStar_Pervasives_Native.None
  
let (unit_binder : FStar_Syntax_Syntax.binder) =
  let uu____1468 =
    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
      FStar_Syntax_Syntax.t_unit
     in
  FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____1468 
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
      (let uu____1546 = FStar_List.hd l  in
       match uu____1546 with
       | (p1,w1,e1) ->
           let uu____1580 =
             let uu____1589 = FStar_List.tl l  in FStar_List.hd uu____1589
              in
           (match uu____1580 with
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
                 | uu____1663 -> def)))
  
let (instantiate :
  FStar_Extraction_ML_Syntax.mltyscheme ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty)
  = fun s  -> fun args  -> FStar_Extraction_ML_Util.subst s args 
let (erasable :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.e_tag ->
      FStar_Extraction_ML_Syntax.mlty -> Prims.bool)
  =
  fun g  ->
    fun f  ->
      fun t  ->
        (f = FStar_Extraction_ML_Syntax.E_GHOST) ||
          ((f = FStar_Extraction_ML_Syntax.E_PURE) && (erasableType g t))
  
let (erase :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.mlexpr ->
      FStar_Extraction_ML_Syntax.mlty ->
        FStar_Extraction_ML_Syntax.e_tag ->
          (FStar_Extraction_ML_Syntax.mlexpr,FStar_Extraction_ML_Syntax.e_tag,
            FStar_Extraction_ML_Syntax.mlty) FStar_Pervasives_Native.tuple3)
  =
  fun g  ->
    fun e  ->
      fun ty  ->
        fun f  ->
          let e1 =
            let uu____1720 = erasable g f ty  in
            if uu____1720
            then
              let uu____1721 =
                type_leq g ty FStar_Extraction_ML_Syntax.ml_unit_ty  in
              (if uu____1721
               then FStar_Extraction_ML_Syntax.ml_unit
               else
                 FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty)
                   (FStar_Extraction_ML_Syntax.MLE_Coerce
                      (FStar_Extraction_ML_Syntax.ml_unit,
                        FStar_Extraction_ML_Syntax.ml_unit_ty, ty)))
            else e  in
          (e1, f, ty)
  
let (eta_expand :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun t  ->
    fun e  ->
      let uu____1730 = FStar_Extraction_ML_Util.doms_and_cod t  in
      match uu____1730 with
      | (ts,r) ->
          if ts = []
          then e
          else
            (let vs = FStar_List.map (fun uu____1750  -> fresh "a") ts  in
             let vs_ts = FStar_List.zip vs ts  in
             let vs_es =
               let uu____1761 = FStar_List.zip vs ts  in
               FStar_List.map
                 (fun uu____1775  ->
                    match uu____1775 with
                    | (v1,t1) ->
                        FStar_Extraction_ML_Syntax.with_ty t1
                          (FStar_Extraction_ML_Syntax.MLE_Var v1)) uu____1761
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
      let uu____1797 =
        (FStar_Options.ml_no_eta_expand_coertions ()) ||
          (let uu____1799 = FStar_Options.codegen ()  in
           uu____1799 = (FStar_Pervasives_Native.Some FStar_Options.Kremlin))
         in
      if uu____1797 then e else eta_expand expect e
  
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
          let uu____1818 =
            type_leq_c g (FStar_Pervasives_Native.Some e) ty1 expect  in
          match uu____1818 with
          | (true ,FStar_Pervasives_Native.Some e') -> e'
          | uu____1828 ->
              (FStar_Extraction_ML_UEnv.debug g
                 (fun uu____1840  ->
                    let uu____1841 =
                      FStar_Extraction_ML_Code.string_of_mlexpr
                        g.FStar_Extraction_ML_UEnv.currentModule e
                       in
                    let uu____1842 =
                      FStar_Extraction_ML_Code.string_of_mlty
                        g.FStar_Extraction_ML_UEnv.currentModule ty1
                       in
                    let uu____1843 =
                      FStar_Extraction_ML_Code.string_of_mlty
                        g.FStar_Extraction_ML_UEnv.currentModule expect
                       in
                    FStar_Util.print3
                      "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n"
                      uu____1841 uu____1842 uu____1843);
               (let uu____1844 =
                  FStar_All.pipe_left
                    (FStar_Extraction_ML_Syntax.with_ty expect)
                    (FStar_Extraction_ML_Syntax.MLE_Coerce (e, ty1, expect))
                   in
                maybe_eta_expand expect uu____1844))
  
let (bv_as_mlty :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun bv  ->
      let uu____1851 = FStar_Extraction_ML_UEnv.lookup_bv g bv  in
      match uu____1851 with
      | FStar_Util.Inl (uu____1852,t) -> t
      | uu____1866 -> FStar_Extraction_ML_Syntax.MLTY_Top
  
let rec (term_as_mlty :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun t0  ->
      let rec is_top_ty t =
        match t with
        | FStar_Extraction_ML_Syntax.MLTY_Top  -> true
        | FStar_Extraction_ML_Syntax.MLTY_Named uu____1909 ->
            let uu____1916 = FStar_Extraction_ML_Util.udelta_unfold g t  in
            (match uu____1916 with
             | FStar_Pervasives_Native.None  -> false
             | FStar_Pervasives_Native.Some t1 -> is_top_ty t1)
        | uu____1920 -> false  in
      let t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.Iota;
          FStar_TypeChecker_Normalize.Zeta;
          FStar_TypeChecker_Normalize.Inlining;
          FStar_TypeChecker_Normalize.EraseUniverses;
          FStar_TypeChecker_Normalize.AllowUnboundUniverses]
          g.FStar_Extraction_ML_UEnv.tcenv t0
         in
      let mlt = term_as_mlty' g t  in
      let uu____1923 = is_top_ty mlt  in
      if uu____1923
      then
        let t1 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Normalize.Beta;
            FStar_TypeChecker_Normalize.Eager_unfolding;
            FStar_TypeChecker_Normalize.UnfoldUntil
              FStar_Syntax_Syntax.Delta_constant;
            FStar_TypeChecker_Normalize.Iota;
            FStar_TypeChecker_Normalize.Zeta;
            FStar_TypeChecker_Normalize.Inlining;
            FStar_TypeChecker_Normalize.EraseUniverses;
            FStar_TypeChecker_Normalize.AllowUnboundUniverses]
            g.FStar_Extraction_ML_UEnv.tcenv t0
           in
        term_as_mlty' g t1
      else mlt

and (term_as_mlty' :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_bvar uu____1929 ->
          let uu____1930 =
            let uu____1931 = FStar_Syntax_Print.term_to_string t1  in
            FStar_Util.format1 "Impossible: Unexpected term %s" uu____1931
             in
          failwith uu____1930
      | FStar_Syntax_Syntax.Tm_delayed uu____1932 ->
          let uu____1957 =
            let uu____1958 = FStar_Syntax_Print.term_to_string t1  in
            FStar_Util.format1 "Impossible: Unexpected term %s" uu____1958
             in
          failwith uu____1957
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____1959 =
            let uu____1960 = FStar_Syntax_Print.term_to_string t1  in
            FStar_Util.format1 "Impossible: Unexpected term %s" uu____1960
             in
          failwith uu____1959
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____1962 = FStar_Syntax_Util.unfold_lazy i  in
          term_as_mlty' env uu____1962
      | FStar_Syntax_Syntax.Tm_constant uu____1963 ->
          FStar_Extraction_ML_UEnv.unknownType
      | FStar_Syntax_Syntax.Tm_quoted uu____1964 ->
          FStar_Extraction_ML_UEnv.unknownType
      | FStar_Syntax_Syntax.Tm_uvar uu____1971 ->
          FStar_Extraction_ML_UEnv.unknownType
      | FStar_Syntax_Syntax.Tm_meta (t2,uu____1989) -> term_as_mlty' env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____1994;
             FStar_Syntax_Syntax.index = uu____1995;
             FStar_Syntax_Syntax.sort = t2;_},uu____1997)
          -> term_as_mlty' env t2
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____2005) -> term_as_mlty' env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____2011,uu____2012) ->
          term_as_mlty' env t2
      | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
      | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv []
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____2079 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____2079 with
           | (bs1,c1) ->
               let uu____2086 = binders_as_ml_binders env bs1  in
               (match uu____2086 with
                | (mlbs,env1) ->
                    let t_ret =
                      let eff =
                        FStar_TypeChecker_Env.norm_eff_name
                          env1.FStar_Extraction_ML_UEnv.tcenv
                          (FStar_Syntax_Util.comp_effect_name c1)
                         in
                      let uu____2113 =
                        let uu____2120 =
                          FStar_TypeChecker_Env.effect_decl_opt
                            env1.FStar_Extraction_ML_UEnv.tcenv eff
                           in
                        FStar_Util.must uu____2120  in
                      match uu____2113 with
                      | (ed,qualifiers) ->
                          let uu____2141 =
                            FStar_All.pipe_right qualifiers
                              (FStar_List.contains
                                 FStar_Syntax_Syntax.Reifiable)
                             in
                          if uu____2141
                          then
                            let t2 =
                              FStar_TypeChecker_Env.reify_comp
                                env1.FStar_Extraction_ML_UEnv.tcenv c1
                                FStar_Syntax_Syntax.U_unknown
                               in
                            let res = term_as_mlty' env1 t2  in res
                          else
                            term_as_mlty' env1
                              (FStar_Syntax_Util.comp_result c1)
                       in
                    let erase1 =
                      effect_as_etag env1
                        (FStar_Syntax_Util.comp_effect_name c1)
                       in
                    let uu____2148 =
                      FStar_List.fold_right
                        (fun uu____2167  ->
                           fun uu____2168  ->
                             match (uu____2167, uu____2168) with
                             | ((uu____2189,t2),(tag,t')) ->
                                 (FStar_Extraction_ML_Syntax.E_PURE,
                                   (FStar_Extraction_ML_Syntax.MLTY_Fun
                                      (t2, tag, t')))) mlbs (erase1, t_ret)
                       in
                    (match uu____2148 with | (uu____2201,t2) -> t2)))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let res =
            let uu____2226 =
              let uu____2227 = FStar_Syntax_Util.un_uinst head1  in
              uu____2227.FStar_Syntax_Syntax.n  in
            match uu____2226 with
            | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
            | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv args
            | FStar_Syntax_Syntax.Tm_app (head2,args') ->
                let uu____2254 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app
                       (head2, (FStar_List.append args' args)))
                    FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   in
                term_as_mlty' env uu____2254
            | uu____2271 -> FStar_Extraction_ML_UEnv.unknownType  in
          res
      | FStar_Syntax_Syntax.Tm_abs (bs,ty,uu____2274) ->
          let uu____2295 = FStar_Syntax_Subst.open_term bs ty  in
          (match uu____2295 with
           | (bs1,ty1) ->
               let uu____2302 = binders_as_ml_binders env bs1  in
               (match uu____2302 with | (bts,env1) -> term_as_mlty' env1 ty1))
      | FStar_Syntax_Syntax.Tm_type uu____2327 ->
          FStar_Extraction_ML_UEnv.unknownType
      | FStar_Syntax_Syntax.Tm_let uu____2328 ->
          FStar_Extraction_ML_UEnv.unknownType
      | FStar_Syntax_Syntax.Tm_match uu____2341 ->
          FStar_Extraction_ML_UEnv.unknownType

and (arg_as_mlty :
  FStar_Extraction_ML_UEnv.env ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun uu____2365  ->
      match uu____2365 with
      | (a,uu____2371) ->
          let uu____2372 = is_type g a  in
          if uu____2372
          then term_as_mlty' g a
          else FStar_Extraction_ML_UEnv.erasedContent

and (fv_app_as_mlty :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.args -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun fv  ->
      fun args  ->
        let uu____2377 =
          let uu____2390 =
            FStar_TypeChecker_Env.lookup_lid g.FStar_Extraction_ML_UEnv.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____2390 with
          | ((uu____2411,fvty),uu____2413) ->
              let fvty1 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Normalize.UnfoldUntil
                     FStar_Syntax_Syntax.Delta_constant]
                  g.FStar_Extraction_ML_UEnv.tcenv fvty
                 in
              FStar_Syntax_Util.arrow_formals fvty1
           in
        match uu____2377 with
        | (formals,uu____2420) ->
            let mlargs = FStar_List.map (arg_as_mlty g) args  in
            let mlargs1 =
              let n_args = FStar_List.length args  in
              if (FStar_List.length formals) > n_args
              then
                let uu____2464 = FStar_Util.first_N n_args formals  in
                match uu____2464 with
                | (uu____2491,rest) ->
                    let uu____2517 =
                      FStar_List.map
                        (fun uu____2525  ->
                           FStar_Extraction_ML_UEnv.erasedContent) rest
                       in
                    FStar_List.append mlargs uu____2517
              else mlargs  in
            let nm =
              let uu____2532 =
                FStar_Extraction_ML_UEnv.maybe_mangle_type_projector g fv  in
              match uu____2532 with
              | FStar_Pervasives_Native.Some p -> p
              | FStar_Pervasives_Native.None  ->
                  FStar_Extraction_ML_Syntax.mlpath_of_lident
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            FStar_Extraction_ML_Syntax.MLTY_Named (mlargs1, nm)

and (binders_as_ml_binders :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.binders ->
      ((FStar_Extraction_ML_Syntax.mlident,FStar_Extraction_ML_Syntax.mlty)
         FStar_Pervasives_Native.tuple2 Prims.list,FStar_Extraction_ML_UEnv.env)
        FStar_Pervasives_Native.tuple2)
  =
  fun g  ->
    fun bs  ->
      let uu____2550 =
        FStar_All.pipe_right bs
          (FStar_List.fold_left
             (fun uu____2593  ->
                fun b  ->
                  match uu____2593 with
                  | (ml_bs,env) ->
                      let uu____2633 = is_type_binder g b  in
                      if uu____2633
                      then
                        let b1 = FStar_Pervasives_Native.fst b  in
                        let env1 =
                          FStar_Extraction_ML_UEnv.extend_ty env b1
                            (FStar_Pervasives_Native.Some
                               FStar_Extraction_ML_Syntax.MLTY_Top)
                           in
                        let ml_b =
                          let uu____2651 =
                            FStar_Extraction_ML_UEnv.bv_as_ml_termvar b1  in
                          (uu____2651, FStar_Extraction_ML_Syntax.ml_unit_ty)
                           in
                        ((ml_b :: ml_bs), env1)
                      else
                        (let b1 = FStar_Pervasives_Native.fst b  in
                         let t = term_as_mlty env b1.FStar_Syntax_Syntax.sort
                            in
                         let uu____2665 =
                           FStar_Extraction_ML_UEnv.extend_bv env b1 
                             ([], t) false false false
                            in
                         match uu____2665 with
                         | (env1,b2) ->
                             let ml_b =
                               let uu____2689 =
                                 FStar_Extraction_ML_UEnv.removeTick b2  in
                               (uu____2689, t)  in
                             ((ml_b :: ml_bs), env1))) ([], g))
         in
      match uu____2550 with | (ml_bs,env) -> ((FStar_List.rev ml_bs), env)

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
      | (FStar_Extraction_ML_Syntax.MLE_Seq es1,uu____2757) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (FStar_List.append es1 [e2])
      | (uu____2760,FStar_Extraction_ML_Syntax.MLE_Seq es2) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (e1 :: es2)
      | uu____2764 -> FStar_Extraction_ML_Syntax.MLE_Seq [e1; e2]
  
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
                    | uu____2792 when
                        (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
                          =
                          FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr
                        -> body.FStar_Extraction_ML_Syntax.expr
                    | uu____2793 ->
                        mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def
                          body)
             | uu____2794 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body))
        | uu____2797 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body)
  
let (resugar_pat :
  FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option ->
    FStar_Extraction_ML_Syntax.mlpattern ->
      FStar_Extraction_ML_Syntax.mlpattern)
  =
  fun q  ->
    fun p  ->
      match p with
      | FStar_Extraction_ML_Syntax.MLP_CTor (d,pats) ->
          let uu____2814 = FStar_Extraction_ML_Util.is_xtuple d  in
          (match uu____2814 with
           | FStar_Pervasives_Native.Some n1 ->
               FStar_Extraction_ML_Syntax.MLP_Tuple pats
           | uu____2818 ->
               (match q with
                | FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Record_ctor (ty,fns)) ->
                    let path =
                      FStar_List.map FStar_Ident.text_of_id ty.FStar_Ident.ns
                       in
                    let fs = record_fields fns pats  in
                    FStar_Extraction_ML_Syntax.MLP_Record (path, fs)
                | uu____2845 -> p))
      | uu____2848 -> p
  
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
                       (fun uu____2928  ->
                          let uu____2929 =
                            FStar_Extraction_ML_Code.string_of_mlty
                              g.FStar_Extraction_ML_UEnv.currentModule t'
                             in
                          let uu____2930 =
                            FStar_Extraction_ML_Code.string_of_mlty
                              g.FStar_Extraction_ML_UEnv.currentModule t
                             in
                          FStar_Util.print2
                            "Expected pattern type %s; got pattern type %s\n"
                            uu____2929 uu____2930)
                   else ();
                   ok)
               in
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int
                (c,swopt)) when
                let uu____2960 = FStar_Options.codegen ()  in
                uu____2960 <>
                  (FStar_Pervasives_Native.Some FStar_Options.Kremlin)
                ->
                let uu____2965 =
                  match swopt with
                  | FStar_Pervasives_Native.None  ->
                      let uu____2978 =
                        let uu____2979 =
                          let uu____2980 =
                            FStar_Extraction_ML_Util.mlconst_of_const
                              p.FStar_Syntax_Syntax.p
                              (FStar_Const.Const_int
                                 (c, FStar_Pervasives_Native.None))
                             in
                          FStar_Extraction_ML_Syntax.MLE_Const uu____2980  in
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.ml_int_ty) uu____2979
                         in
                      (uu____2978, FStar_Extraction_ML_Syntax.ml_int_ty)
                  | FStar_Pervasives_Native.Some sw ->
                      let source_term =
                        FStar_ToSyntax_ToSyntax.desugar_machine_integer
                          (g.FStar_Extraction_ML_UEnv.tcenv).FStar_TypeChecker_Env.dsenv
                          c sw FStar_Range.dummyRange
                         in
                      let uu____3001 = term_as_mlexpr g source_term  in
                      (match uu____3001 with
                       | (mlterm,uu____3013,mlty) -> (mlterm, mlty))
                   in
                (match uu____2965 with
                 | (mlc,ml_ty) ->
                     let x = FStar_Extraction_ML_Syntax.gensym ()  in
                     let when_clause =
                       let uu____3033 =
                         let uu____3034 =
                           let uu____3041 =
                             let uu____3044 =
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty ml_ty)
                                 (FStar_Extraction_ML_Syntax.MLE_Var x)
                                in
                             [uu____3044; mlc]  in
                           (FStar_Extraction_ML_Util.prims_op_equality,
                             uu____3041)
                            in
                         FStar_Extraction_ML_Syntax.MLE_App uu____3034  in
                       FStar_All.pipe_left
                         (FStar_Extraction_ML_Syntax.with_ty
                            FStar_Extraction_ML_Syntax.ml_bool_ty) uu____3033
                        in
                     let uu____3047 = ok ml_ty  in
                     (g,
                       (FStar_Pervasives_Native.Some
                          ((FStar_Extraction_ML_Syntax.MLP_Var x),
                            [when_clause])), uu____3047))
            | FStar_Syntax_Syntax.Pat_constant s ->
                let t =
                  FStar_TypeChecker_TcTerm.tc_constant
                    g.FStar_Extraction_ML_UEnv.tcenv FStar_Range.dummyRange s
                   in
                let mlty = term_as_mlty g t  in
                let uu____3067 =
                  let uu____3076 =
                    let uu____3083 =
                      let uu____3084 =
                        FStar_Extraction_ML_Util.mlconst_of_const
                          p.FStar_Syntax_Syntax.p s
                         in
                      FStar_Extraction_ML_Syntax.MLP_Const uu____3084  in
                    (uu____3083, [])  in
                  FStar_Pervasives_Native.Some uu____3076  in
                let uu____3093 = ok mlty  in (g, uu____3067, uu____3093)
            | FStar_Syntax_Syntax.Pat_var x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort  in
                let uu____3104 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp
                   in
                (match uu____3104 with
                 | (g1,x1) ->
                     let uu____3127 = ok mlty  in
                     (g1,
                       (if imp
                        then FStar_Pervasives_Native.None
                        else
                          FStar_Pervasives_Native.Some
                            ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                       uu____3127))
            | FStar_Syntax_Syntax.Pat_wild x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort  in
                let uu____3161 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp
                   in
                (match uu____3161 with
                 | (g1,x1) ->
                     let uu____3184 = ok mlty  in
                     (g1,
                       (if imp
                        then FStar_Pervasives_Native.None
                        else
                          FStar_Pervasives_Native.Some
                            ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                       uu____3184))
            | FStar_Syntax_Syntax.Pat_dot_term uu____3216 ->
                (g, FStar_Pervasives_Native.None, true)
            | FStar_Syntax_Syntax.Pat_cons (f,pats) ->
                let uu____3255 =
                  let uu____3260 = FStar_Extraction_ML_UEnv.lookup_fv g f  in
                  match uu____3260 with
                  | FStar_Util.Inr
                      (uu____3265,{
                                    FStar_Extraction_ML_Syntax.expr =
                                      FStar_Extraction_ML_Syntax.MLE_Name n1;
                                    FStar_Extraction_ML_Syntax.mlty =
                                      uu____3267;
                                    FStar_Extraction_ML_Syntax.loc =
                                      uu____3268;_},ttys,uu____3270)
                      -> (n1, ttys)
                  | uu____3283 -> failwith "Expected a constructor"  in
                (match uu____3255 with
                 | (d,tys) ->
                     let nTyVars =
                       FStar_List.length (FStar_Pervasives_Native.fst tys)
                        in
                     let uu____3305 = FStar_Util.first_N nTyVars pats  in
                     (match uu____3305 with
                      | (tysVarPats,restPats) ->
                          let f_ty_opt =
                            try
                              let mlty_args =
                                FStar_All.pipe_right tysVarPats
                                  (FStar_List.map
                                     (fun uu____3438  ->
                                        match uu____3438 with
                                        | (p1,uu____3446) ->
                                            (match p1.FStar_Syntax_Syntax.v
                                             with
                                             | FStar_Syntax_Syntax.Pat_dot_term
                                                 (uu____3451,t) ->
                                                 term_as_mlty g t
                                             | uu____3457 ->
                                                 (FStar_Extraction_ML_UEnv.debug
                                                    g
                                                    (fun uu____3461  ->
                                                       let uu____3462 =
                                                         FStar_Syntax_Print.pat_to_string
                                                           p1
                                                          in
                                                       FStar_Util.print1
                                                         "Pattern %s is not extractable"
                                                         uu____3462);
                                                  FStar_Exn.raise
                                                    Un_extractable))))
                                 in
                              let f_ty =
                                FStar_Extraction_ML_Util.subst tys mlty_args
                                 in
                              let uu____3464 =
                                FStar_Extraction_ML_Util.uncurry_mlty_fun
                                  f_ty
                                 in
                              FStar_Pervasives_Native.Some uu____3464
                            with
                            | Un_extractable  -> FStar_Pervasives_Native.None
                             in
                          let uu____3493 =
                            FStar_Util.fold_map
                              (fun g1  ->
                                 fun uu____3529  ->
                                   match uu____3529 with
                                   | (p1,imp1) ->
                                       let uu____3548 =
                                         extract_one_pat true g1 p1
                                           FStar_Pervasives_Native.None
                                           term_as_mlexpr
                                          in
                                       (match uu____3548 with
                                        | (g2,p2,uu____3577) -> (g2, p2))) g
                              tysVarPats
                             in
                          (match uu____3493 with
                           | (g1,tyMLPats) ->
                               let uu____3638 =
                                 FStar_Util.fold_map
                                   (fun uu____3702  ->
                                      fun uu____3703  ->
                                        match (uu____3702, uu____3703) with
                                        | ((g2,f_ty_opt1),(p1,imp1)) ->
                                            let uu____3796 =
                                              match f_ty_opt1 with
                                              | FStar_Pervasives_Native.Some
                                                  (hd1::rest,res) ->
                                                  ((FStar_Pervasives_Native.Some
                                                      (rest, res)),
                                                    (FStar_Pervasives_Native.Some
                                                       hd1))
                                              | uu____3856 ->
                                                  (FStar_Pervasives_Native.None,
                                                    FStar_Pervasives_Native.None)
                                               in
                                            (match uu____3796 with
                                             | (f_ty_opt2,expected_ty) ->
                                                 let uu____3927 =
                                                   extract_one_pat false g2
                                                     p1 expected_ty
                                                     term_as_mlexpr
                                                    in
                                                 (match uu____3927 with
                                                  | (g3,p2,uu____3968) ->
                                                      ((g3, f_ty_opt2), p2))))
                                   (g1, f_ty_opt) restPats
                                  in
                               (match uu____3638 with
                                | ((g2,f_ty_opt1),restMLPats) ->
                                    let uu____4086 =
                                      let uu____4097 =
                                        FStar_All.pipe_right
                                          (FStar_List.append tyMLPats
                                             restMLPats)
                                          (FStar_List.collect
                                             (fun uu___58_4148  ->
                                                match uu___58_4148 with
                                                | FStar_Pervasives_Native.Some
                                                    x -> [x]
                                                | uu____4190 -> []))
                                         in
                                      FStar_All.pipe_right uu____4097
                                        FStar_List.split
                                       in
                                    (match uu____4086 with
                                     | (mlPats,when_clauses) ->
                                         let pat_ty_compat =
                                           match f_ty_opt1 with
                                           | FStar_Pervasives_Native.Some
                                               ([],t) -> ok t
                                           | uu____4263 -> false  in
                                         let uu____4272 =
                                           let uu____4281 =
                                             let uu____4288 =
                                               resugar_pat
                                                 f.FStar_Syntax_Syntax.fv_qual
                                                 (FStar_Extraction_ML_Syntax.MLP_CTor
                                                    (d, mlPats))
                                                in
                                             let uu____4291 =
                                               FStar_All.pipe_right
                                                 when_clauses
                                                 FStar_List.flatten
                                                in
                                             (uu____4288, uu____4291)  in
                                           FStar_Pervasives_Native.Some
                                             uu____4281
                                            in
                                         (g2, uu____4272, pat_ty_compat))))))
  
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
            let uu____4404 =
              extract_one_pat false g1 p1 expected_t1 term_as_mlexpr  in
            match uu____4404 with
            | (g2,FStar_Pervasives_Native.Some (x,v1),b) -> (g2, (x, v1), b)
            | uu____4461 ->
                failwith "Impossible: Unable to translate pattern"
             in
          let mk_when_clause whens =
            match whens with
            | [] -> FStar_Pervasives_Native.None
            | hd1::tl1 ->
                let uu____4504 =
                  FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd1
                    tl1
                   in
                FStar_Pervasives_Native.Some uu____4504
             in
          let uu____4505 =
            extract_one_pat1 g p (FStar_Pervasives_Native.Some expected_t)
             in
          match uu____4505 with
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
            | FStar_Extraction_ML_Syntax.MLTY_Fun (t0,uu____4643,t1) ->
                let x = FStar_Extraction_ML_Syntax.gensym ()  in
                let uu____4646 =
                  let uu____4657 =
                    let uu____4666 =
                      FStar_All.pipe_left
                        (FStar_Extraction_ML_Syntax.with_ty t0)
                        (FStar_Extraction_ML_Syntax.MLE_Var x)
                       in
                    ((x, t0), uu____4666)  in
                  uu____4657 :: more_args  in
                eta_args uu____4646 t1
            | FStar_Extraction_ML_Syntax.MLTY_Named (uu____4679,uu____4680)
                -> ((FStar_List.rev more_args), t)
            | uu____4703 -> failwith "Impossible: Head type is not an arrow"
             in
          let as_record qual1 e =
            match ((e.FStar_Extraction_ML_Syntax.expr), qual1) with
            | (FStar_Extraction_ML_Syntax.MLE_CTor
               (uu____4731,args),FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Record_ctor (tyname,fields))) ->
                let path =
                  FStar_List.map FStar_Ident.text_of_id tyname.FStar_Ident.ns
                   in
                let fields1 = record_fields fields args  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     e.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_Record (path, fields1))
            | uu____4763 -> e  in
          let resugar_and_maybe_eta qual1 e =
            let uu____4781 = eta_args [] residualType  in
            match uu____4781 with
            | (eargs,tres) ->
                (match eargs with
                 | [] ->
                     let uu____4834 = as_record qual1 e  in
                     FStar_Extraction_ML_Util.resugar_exp uu____4834
                 | uu____4835 ->
                     let uu____4846 = FStar_List.unzip eargs  in
                     (match uu____4846 with
                      | (binders,eargs1) ->
                          (match e.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_CTor (head1,args)
                               ->
                               let body =
                                 let uu____4888 =
                                   let uu____4889 =
                                     FStar_All.pipe_left
                                       (FStar_Extraction_ML_Syntax.with_ty
                                          tres)
                                       (FStar_Extraction_ML_Syntax.MLE_CTor
                                          (head1,
                                            (FStar_List.append args eargs1)))
                                      in
                                   FStar_All.pipe_left (as_record qual1)
                                     uu____4889
                                    in
                                 FStar_All.pipe_left
                                   FStar_Extraction_ML_Util.resugar_exp
                                   uu____4888
                                  in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    e.FStar_Extraction_ML_Syntax.mlty)
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    (binders, body))
                           | uu____4898 ->
                               failwith "Impossible: Not a constructor")))
             in
          match ((mlAppExpr.FStar_Extraction_ML_Syntax.expr), qual) with
          | (uu____4901,FStar_Pervasives_Native.None ) -> mlAppExpr
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____4905;
                FStar_Extraction_ML_Syntax.loc = uu____4906;_},mle::args),FStar_Pervasives_Native.Some
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
                | uu____4933 ->
                    let uu____4936 =
                      let uu____4943 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj
                         in
                      (uu____4943, args)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____4936
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
                     FStar_Extraction_ML_Syntax.mlty = uu____4947;
                     FStar_Extraction_ML_Syntax.loc = uu____4948;_},uu____4949);
                FStar_Extraction_ML_Syntax.mlty = uu____4950;
                FStar_Extraction_ML_Syntax.loc = uu____4951;_},mle::args),FStar_Pervasives_Native.Some
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
                | uu____4982 ->
                    let uu____4985 =
                      let uu____4992 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj
                         in
                      (uu____4992, args)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____4985
                 in
              FStar_Extraction_ML_Syntax.with_ty
                mlAppExpr.FStar_Extraction_ML_Syntax.mlty e
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____4996;
                FStar_Extraction_ML_Syntax.loc = uu____4997;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____5005 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5005
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____5009;
                FStar_Extraction_ML_Syntax.loc = uu____5010;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____5012)) ->
              let uu____5025 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5025
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____5029;
                     FStar_Extraction_ML_Syntax.loc = uu____5030;_},uu____5031);
                FStar_Extraction_ML_Syntax.mlty = uu____5032;
                FStar_Extraction_ML_Syntax.loc = uu____5033;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____5045 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5045
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____5049;
                     FStar_Extraction_ML_Syntax.loc = uu____5050;_},uu____5051);
                FStar_Extraction_ML_Syntax.mlty = uu____5052;
                FStar_Extraction_ML_Syntax.loc = uu____5053;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____5055)) ->
              let uu____5072 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5072
          | (FStar_Extraction_ML_Syntax.MLE_Name
             mlp,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor
             )) ->
              let uu____5078 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5078
          | (FStar_Extraction_ML_Syntax.MLE_Name
             mlp,FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____5082)) ->
              let uu____5091 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5091
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____5095;
                FStar_Extraction_ML_Syntax.loc = uu____5096;_},uu____5097),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____5104 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5104
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____5108;
                FStar_Extraction_ML_Syntax.loc = uu____5109;_},uu____5110),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____5111)) ->
              let uu____5124 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5124
          | uu____5127 -> mlAppExpr
  
let (maybe_downgrade_eff :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.e_tag ->
      FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.e_tag)
  =
  fun g  ->
    fun f  ->
      fun t  ->
        let rec non_informative1 t1 =
          let uu____5147 =
            (type_leq g t1 FStar_Extraction_ML_Syntax.ml_unit_ty) ||
              (erasableType g t1)
             in
          if uu____5147
          then true
          else
            (match t1 with
             | FStar_Extraction_ML_Syntax.MLTY_Fun
                 (uu____5149,FStar_Extraction_ML_Syntax.E_PURE ,t2) ->
                 non_informative1 t2
             | FStar_Extraction_ML_Syntax.MLTY_Fun
                 (uu____5151,FStar_Extraction_ML_Syntax.E_GHOST ,t2) ->
                 non_informative1 t2
             | uu____5153 -> false)
           in
        let uu____5154 =
          (f = FStar_Extraction_ML_Syntax.E_GHOST) && (non_informative1 t)
           in
        if uu____5154 then FStar_Extraction_ML_Syntax.E_PURE else f
  
let rec (term_as_mlexpr :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Extraction_ML_Syntax.mlexpr,FStar_Extraction_ML_Syntax.e_tag,
        FStar_Extraction_ML_Syntax.mlty) FStar_Pervasives_Native.tuple3)
  =
  fun g  ->
    fun t  ->
      let uu____5208 = term_as_mlexpr' g t  in
      match uu____5208 with
      | (e,tag,ty) ->
          let tag1 = maybe_downgrade_eff g tag ty  in
          (FStar_Extraction_ML_UEnv.debug g
             (fun u  ->
                let uu____5229 =
                  let uu____5230 = FStar_Syntax_Print.tag_of_term t  in
                  let uu____5231 = FStar_Syntax_Print.term_to_string t  in
                  let uu____5232 =
                    FStar_Extraction_ML_Code.string_of_mlty
                      g.FStar_Extraction_ML_UEnv.currentModule ty
                     in
                  let uu____5233 =
                    FStar_Extraction_ML_Util.eff_to_string tag1  in
                  FStar_Util.format4
                    "term_as_mlexpr (%s) :  %s has ML type %s and effect %s\n"
                    uu____5230 uu____5231 uu____5232 uu____5233
                   in
                FStar_Util.print_string uu____5229);
           erase g e ty tag1)

and (check_term_as_mlexpr :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Extraction_ML_Syntax.e_tag ->
        FStar_Extraction_ML_Syntax.mlty ->
          (FStar_Extraction_ML_Syntax.mlexpr,FStar_Extraction_ML_Syntax.mlty)
            FStar_Pervasives_Native.tuple2)
  =
  fun g  ->
    fun t  ->
      fun f  ->
        fun ty  ->
          let uu____5242 = check_term_as_mlexpr' g t f ty  in
          match uu____5242 with
          | (e,t1) ->
              let uu____5253 = erase g e t1 f  in
              (match uu____5253 with | (r,uu____5265,t2) -> (r, t2))

and (check_term_as_mlexpr' :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Extraction_ML_Syntax.e_tag ->
        FStar_Extraction_ML_Syntax.mlty ->
          (FStar_Extraction_ML_Syntax.mlexpr,FStar_Extraction_ML_Syntax.mlty)
            FStar_Pervasives_Native.tuple2)
  =
  fun g  ->
    fun e0  ->
      fun f  ->
        fun ty  ->
          let uu____5275 = term_as_mlexpr g e0  in
          match uu____5275 with
          | (e,tag,t) ->
              let tag1 = maybe_downgrade_eff g tag t  in
              let uu____5290 = FStar_Extraction_ML_Util.eff_leq tag1 f  in
              if uu____5290
              then
                let uu____5295 = maybe_coerce g e t ty  in (uu____5295, ty)
              else
                (err_unexpected_eff g e0 ty f tag1;
                 (let uu____5298 = maybe_coerce g e t ty  in (uu____5298, ty)))

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
           let uu____5311 =
             let uu____5312 =
               FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos  in
             let uu____5313 = FStar_Syntax_Print.tag_of_term top  in
             let uu____5314 = FStar_Syntax_Print.term_to_string top  in
             FStar_Util.format3 "%s: term_as_mlexpr' (%s) :  %s \n"
               uu____5312 uu____5313 uu____5314
              in
           FStar_Util.print_string uu____5311);
      (let t = FStar_Syntax_Subst.compress top  in
       match t.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____5322 =
             let uu____5323 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5323
              in
           failwith uu____5322
       | FStar_Syntax_Syntax.Tm_delayed uu____5330 ->
           let uu____5355 =
             let uu____5356 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5356
              in
           failwith uu____5355
       | FStar_Syntax_Syntax.Tm_uvar uu____5363 ->
           let uu____5380 =
             let uu____5381 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5381
              in
           failwith uu____5380
       | FStar_Syntax_Syntax.Tm_bvar uu____5388 ->
           let uu____5389 =
             let uu____5390 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5390
              in
           failwith uu____5389
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____5398 = FStar_Syntax_Util.unfold_lazy i  in
           term_as_mlexpr' g uu____5398
       | FStar_Syntax_Syntax.Tm_type uu____5399 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_refine uu____5400 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_arrow uu____5407 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_quoted
           (qt,{
                 FStar_Syntax_Syntax.qkind =
                   FStar_Syntax_Syntax.Quote_dynamic ;_})
           ->
           let uu____5425 =
             let uu____5434 =
               let uu____5451 =
                 FStar_Syntax_Syntax.lid_as_fv
                   FStar_Parser_Const.failwith_lid
                   FStar_Syntax_Syntax.Delta_constant
                   FStar_Pervasives_Native.None
                  in
               FStar_Extraction_ML_UEnv.lookup_fv g uu____5451  in
             FStar_All.pipe_left FStar_Util.right uu____5434  in
           (match uu____5425 with
            | (uu____5494,fw,uu____5496,uu____5497) ->
                let uu____5498 =
                  let uu____5499 =
                    let uu____5500 =
                      let uu____5507 =
                        let uu____5510 =
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty
                               FStar_Extraction_ML_Syntax.ml_string_ty)
                            (FStar_Extraction_ML_Syntax.MLE_Const
                               (FStar_Extraction_ML_Syntax.MLC_String
                                  "Open quotation at runtime"))
                           in
                        [uu____5510]  in
                      (fw, uu____5507)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____5500  in
                  FStar_All.pipe_left
                    (FStar_Extraction_ML_Syntax.with_ty
                       FStar_Extraction_ML_Syntax.ml_int_ty) uu____5499
                   in
                (uu____5498, FStar_Extraction_ML_Syntax.E_PURE,
                  FStar_Extraction_ML_Syntax.ml_int_ty))
       | FStar_Syntax_Syntax.Tm_quoted
           (qt,{
                 FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static ;_})
           ->
           let tv =
             let uu____5519 = FStar_Reflection_Basic.inspect_ln qt  in
             FStar_Reflection_Embeddings.embed_term_view
               t.FStar_Syntax_Syntax.pos uu____5519
              in
           let t1 =
             let uu____5523 =
               let uu____5532 = FStar_Syntax_Syntax.as_arg tv  in
               [uu____5532]  in
             FStar_Syntax_Util.mk_app
               (FStar_Reflection_Data.refl_constant_term
                  FStar_Reflection_Data.fstar_refl_pack_ln) uu____5523
              in
           term_as_mlexpr' g t1
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Mutable_alloc ))
           ->
           FStar_Errors.raise_err
             (FStar_Errors.Error_NoLetMutable,
               "let-mutable no longer supported")
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_monadic (m,uu____5546)) ->
           let t2 = FStar_Syntax_Subst.compress t1  in
           (match t2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) when
                FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname ->
                let uu____5576 =
                  let uu____5583 =
                    FStar_TypeChecker_Env.effect_decl_opt
                      g.FStar_Extraction_ML_UEnv.tcenv m
                     in
                  FStar_Util.must uu____5583  in
                (match uu____5576 with
                 | (ed,qualifiers) ->
                     let uu____5610 =
                       let uu____5611 =
                         FStar_All.pipe_right qualifiers
                           (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                          in
                       FStar_All.pipe_right uu____5611 Prims.op_Negation  in
                     if uu____5610
                     then term_as_mlexpr' g t2
                     else
                       failwith
                         "This should not happen (should have been handled at Tm_abs level)")
            | uu____5627 -> term_as_mlexpr' g t2)
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____5629) -> term_as_mlexpr' g t1
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____5635) -> term_as_mlexpr' g t1
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____5641 =
             FStar_TypeChecker_TcTerm.type_of_tot_term
               g.FStar_Extraction_ML_UEnv.tcenv t
              in
           (match uu____5641 with
            | (uu____5654,ty,uu____5656) ->
                let ml_ty = term_as_mlty g ty  in
                let uu____5658 =
                  let uu____5659 =
                    FStar_Extraction_ML_Util.mlexpr_of_const
                      t.FStar_Syntax_Syntax.pos c
                     in
                  FStar_Extraction_ML_Syntax.with_ty ml_ty uu____5659  in
                (uu____5658, FStar_Extraction_ML_Syntax.E_PURE, ml_ty))
       | FStar_Syntax_Syntax.Tm_name uu____5660 ->
           let uu____5661 = is_type g t  in
           if uu____5661
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____5669 = FStar_Extraction_ML_UEnv.lookup_term g t  in
              match uu____5669 with
              | (FStar_Util.Inl uu____5682,uu____5683) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | (FStar_Util.Inr (uu____5720,x,mltys,uu____5723),qual) ->
                  (match mltys with
                   | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                       ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | ([],t1) ->
                       let uu____5769 =
                         maybe_eta_data_and_project_record g qual t1 x  in
                       (uu____5769, FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | uu____5770 -> err_uninst g t mltys t))
       | FStar_Syntax_Syntax.Tm_fvar uu____5777 ->
           let uu____5778 = is_type g t  in
           if uu____5778
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____5786 = FStar_Extraction_ML_UEnv.lookup_term g t  in
              match uu____5786 with
              | (FStar_Util.Inl uu____5799,uu____5800) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | (FStar_Util.Inr (uu____5837,x,mltys,uu____5840),qual) ->
                  (match mltys with
                   | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                       ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | ([],t1) ->
                       let uu____5886 =
                         maybe_eta_data_and_project_record g qual t1 x  in
                       (uu____5886, FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | uu____5887 -> err_uninst g t mltys t))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,copt) ->
           let uu____5917 = FStar_Syntax_Subst.open_term bs body  in
           (match uu____5917 with
            | (bs1,body1) ->
                let uu____5930 = binders_as_ml_binders g bs1  in
                (match uu____5930 with
                 | (ml_bs,env) ->
                     let body2 =
                       match copt with
                       | FStar_Pervasives_Native.Some c ->
                           let uu____5963 =
                             FStar_TypeChecker_Env.is_reifiable
                               env.FStar_Extraction_ML_UEnv.tcenv c
                              in
                           if uu____5963
                           then
                             FStar_TypeChecker_Util.reify_body
                               env.FStar_Extraction_ML_UEnv.tcenv body1
                           else body1
                       | FStar_Pervasives_Native.None  ->
                           (FStar_Extraction_ML_UEnv.debug g
                              (fun uu____5968  ->
                                 let uu____5969 =
                                   FStar_Syntax_Print.term_to_string body1
                                    in
                                 FStar_Util.print1
                                   "No computation type for: %s\n" uu____5969);
                            body1)
                        in
                     let uu____5970 = term_as_mlexpr env body2  in
                     (match uu____5970 with
                      | (ml_body,f,t1) ->
                          let uu____5986 =
                            FStar_List.fold_right
                              (fun uu____6005  ->
                                 fun uu____6006  ->
                                   match (uu____6005, uu____6006) with
                                   | ((uu____6027,targ),(f1,t2)) ->
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         (FStar_Extraction_ML_Syntax.MLTY_Fun
                                            (targ, f1, t2)))) ml_bs (f, t1)
                             in
                          (match uu____5986 with
                           | (f1,tfun) ->
                               let uu____6047 =
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty tfun)
                                   (FStar_Extraction_ML_Syntax.MLE_Fun
                                      (ml_bs, ml_body))
                                  in
                               (uu____6047, f1, tfun)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____6054;
              FStar_Syntax_Syntax.vars = uu____6055;_},(a1,uu____6057)::[])
           ->
           let ty =
             let uu____6087 =
               FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid  in
             term_as_mlty g uu____6087  in
           let uu____6088 =
             let uu____6089 =
               FStar_Extraction_ML_Util.mlexpr_of_range
                 a1.FStar_Syntax_Syntax.pos
                in
             FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty)
               uu____6089
              in
           (uu____6088, FStar_Extraction_ML_Syntax.E_PURE, ty)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____6090;
              FStar_Syntax_Syntax.vars = uu____6091;_},(t1,uu____6093)::
            (r,uu____6095)::[])
           -> term_as_mlexpr' g t1
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____6134);
              FStar_Syntax_Syntax.pos = uu____6135;
              FStar_Syntax_Syntax.vars = uu____6136;_},uu____6137)
           -> failwith "Unreachable? Tm_app Const_reflect"
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let is_total rc =
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_Tot_lid)
               ||
               (FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
                  (FStar_List.existsb
                     (fun uu___59_6193  ->
                        match uu___59_6193 with
                        | FStar_Syntax_Syntax.TOTAL  -> true
                        | uu____6194 -> false)))
              in
           let uu____6195 =
             let uu____6200 =
               let uu____6201 = FStar_Syntax_Subst.compress head1  in
               uu____6201.FStar_Syntax_Syntax.n  in
             ((head1.FStar_Syntax_Syntax.n), uu____6200)  in
           (match uu____6195 with
            | (FStar_Syntax_Syntax.Tm_uvar uu____6210,uu____6211) ->
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
            | (uu____6229,FStar_Syntax_Syntax.Tm_abs
               (bs,uu____6231,FStar_Pervasives_Native.Some rc)) when
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
            | (uu____6252,FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_reify )) ->
                let e =
                  let uu____6254 = FStar_List.hd args  in
                  FStar_TypeChecker_Util.reify_body_with_arg
                    g.FStar_Extraction_ML_UEnv.tcenv head1 uu____6254
                   in
                let tm =
                  let uu____6264 =
                    let uu____6265 = FStar_TypeChecker_Util.remove_reify e
                       in
                    let uu____6266 = FStar_List.tl args  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____6265 uu____6266  in
                  uu____6264 FStar_Pervasives_Native.None
                    t.FStar_Syntax_Syntax.pos
                   in
                term_as_mlexpr' g tm
            | uu____6275 ->
                let rec extract_app is_data uu____6320 uu____6321 restArgs =
                  match (uu____6320, uu____6321) with
                  | ((mlhead,mlargs_f),(f,t1)) ->
                      (match (restArgs, t1) with
                       | ([],uu____6411) ->
                           let evaluation_order_guaranteed =
                             (((FStar_List.length mlargs_f) =
                                 (Prims.parse_int "1"))
                                ||
                                (FStar_Extraction_ML_Util.codegen_fsharp ()))
                               ||
                               (match head1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_fvar fv ->
                                    (FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.op_And)
                                      ||
                                      (FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.op_Or)
                                | uu____6433 -> false)
                              in
                           let uu____6434 =
                             if evaluation_order_guaranteed
                             then
                               let uu____6459 =
                                 FStar_All.pipe_right
                                   (FStar_List.rev mlargs_f)
                                   (FStar_List.map
                                      FStar_Pervasives_Native.fst)
                                  in
                               ([], uu____6459)
                             else
                               FStar_List.fold_left
                                 (fun uu____6513  ->
                                    fun uu____6514  ->
                                      match (uu____6513, uu____6514) with
                                      | ((lbs,out_args),(arg,f1)) ->
                                          if
                                            (f1 =
                                               FStar_Extraction_ML_Syntax.E_PURE)
                                              ||
                                              (f1 =
                                                 FStar_Extraction_ML_Syntax.E_GHOST)
                                          then (lbs, (arg :: out_args))
                                          else
                                            (let x =
                                               FStar_Extraction_ML_Syntax.gensym
                                                 ()
                                                in
                                             let uu____6617 =
                                               let uu____6620 =
                                                 FStar_All.pipe_left
                                                   (FStar_Extraction_ML_Syntax.with_ty
                                                      arg.FStar_Extraction_ML_Syntax.mlty)
                                                   (FStar_Extraction_ML_Syntax.MLE_Var
                                                      x)
                                                  in
                                               uu____6620 :: out_args  in
                                             (((x, arg) :: lbs), uu____6617)))
                                 ([], []) mlargs_f
                              in
                           (match uu____6434 with
                            | (lbs,mlargs) ->
                                let app =
                                  let uu____6670 =
                                    FStar_All.pipe_left
                                      (FStar_Extraction_ML_Syntax.with_ty t1)
                                      (FStar_Extraction_ML_Syntax.MLE_App
                                         (mlhead, mlargs))
                                     in
                                  FStar_All.pipe_left
                                    (maybe_eta_data_and_project_record g
                                       is_data t1) uu____6670
                                   in
                                let l_app =
                                  FStar_List.fold_right
                                    (fun uu____6682  ->
                                       fun out  ->
                                         match uu____6682 with
                                         | (x,arg) ->
                                             FStar_All.pipe_left
                                               (FStar_Extraction_ML_Syntax.with_ty
                                                  out.FStar_Extraction_ML_Syntax.mlty)
                                               (mk_MLE_Let false
                                                  (FStar_Extraction_ML_Syntax.NonRec,
                                                    [{
                                                       FStar_Extraction_ML_Syntax.mllb_name
                                                         = x;
                                                       FStar_Extraction_ML_Syntax.mllb_tysc
                                                         =
                                                         (FStar_Pervasives_Native.Some
                                                            ([],
                                                              (arg.FStar_Extraction_ML_Syntax.mlty)));
                                                       FStar_Extraction_ML_Syntax.mllb_add_unit
                                                         = false;
                                                       FStar_Extraction_ML_Syntax.mllb_def
                                                         = arg;
                                                       FStar_Extraction_ML_Syntax.mllb_meta
                                                         = [];
                                                       FStar_Extraction_ML_Syntax.print_typ
                                                         = true
                                                     }]) out)) lbs app
                                   in
                                (l_app, f, t1))
                       | ((arg,uu____6701)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                          (formal_t,f',t2)) when
                           (is_type g arg) &&
                             (type_leq g formal_t
                                FStar_Extraction_ML_Syntax.ml_unit_ty)
                           ->
                           let uu____6732 =
                             let uu____6737 =
                               FStar_Extraction_ML_Util.join
                                 arg.FStar_Syntax_Syntax.pos f f'
                                in
                             (uu____6737, t2)  in
                           extract_app is_data
                             (mlhead,
                               ((FStar_Extraction_ML_Syntax.ml_unit,
                                  FStar_Extraction_ML_Syntax.E_PURE) ::
                               mlargs_f)) uu____6732 rest
                       | ((e0,uu____6749)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                          (tExpected,f',t2)) ->
                           let r = e0.FStar_Syntax_Syntax.pos  in
                           let uu____6781 = term_as_mlexpr g e0  in
                           (match uu____6781 with
                            | (e01,f0,tInferred) ->
                                let e02 =
                                  maybe_coerce g e01 tInferred tExpected  in
                                let uu____6798 =
                                  let uu____6803 =
                                    FStar_Extraction_ML_Util.join_l r
                                      [f; f'; f0]
                                     in
                                  (uu____6803, t2)  in
                                extract_app is_data
                                  (mlhead, ((e02, f0) :: mlargs_f))
                                  uu____6798 rest)
                       | uu____6814 ->
                           let uu____6827 =
                             FStar_Extraction_ML_Util.udelta_unfold g t1  in
                           (match uu____6827 with
                            | FStar_Pervasives_Native.Some t2 ->
                                extract_app is_data (mlhead, mlargs_f)
                                  (f, t2) restArgs
                            | FStar_Pervasives_Native.None  ->
                                err_ill_typed_application g top restArgs t1))
                   in
                let extract_app_maybe_projector is_data mlhead uu____6884
                  args1 =
                  match uu____6884 with
                  | (f,t1) ->
                      (match is_data with
                       | FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_projector uu____6916)
                           ->
                           let rec remove_implicits args2 f1 t2 =
                             match (args2, t2) with
                             | ((a0,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____6994))::args3,FStar_Extraction_ML_Syntax.MLTY_Fun
                                (uu____6996,f',t3)) ->
                                 let uu____7033 =
                                   FStar_Extraction_ML_Util.join
                                     a0.FStar_Syntax_Syntax.pos f1 f'
                                    in
                                 remove_implicits args3 uu____7033 t3
                             | uu____7034 -> (args2, f1, t2)  in
                           let uu____7059 = remove_implicits args1 f t1  in
                           (match uu____7059 with
                            | (args2,f1,t2) ->
                                extract_app is_data (mlhead, []) (f1, t2)
                                  args2)
                       | uu____7115 ->
                           extract_app is_data (mlhead, []) (f, t1) args1)
                   in
                let uu____7128 = is_type g t  in
                if uu____7128
                then
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
                else
                  (let head2 = FStar_Syntax_Util.un_uinst head1  in
                   match head2.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_name uu____7143 ->
                       let uu____7144 =
                         let uu____7157 =
                           FStar_Extraction_ML_UEnv.lookup_term g head2  in
                         match uu____7157 with
                         | (FStar_Util.Inr (uu____7176,x1,x2,x3),q) ->
                             ((x1, x2, x3), q)
                         | uu____7221 -> failwith "FIXME Ty"  in
                       (match uu____7144 with
                        | ((head_ml,(vars,t1),inst_ok),qual) ->
                            let has_typ_apps =
                              match args with
                              | (a,uu____7271)::uu____7272 -> is_type g a
                              | uu____7291 -> false  in
                            let uu____7300 =
                              match vars with
                              | uu____7329::uu____7330 when
                                  (Prims.op_Negation has_typ_apps) && inst_ok
                                  -> (head_ml, t1, args)
                              | uu____7341 ->
                                  let n1 = FStar_List.length vars  in
                                  if n1 <= (FStar_List.length args)
                                  then
                                    let uu____7369 =
                                      FStar_Util.first_N n1 args  in
                                    (match uu____7369 with
                                     | (prefix1,rest) ->
                                         let prefixAsMLTypes =
                                           FStar_List.map
                                             (fun uu____7458  ->
                                                match uu____7458 with
                                                | (x,uu____7464) ->
                                                    term_as_mlty g x) prefix1
                                            in
                                         let t2 =
                                           instantiate (vars, t1)
                                             prefixAsMLTypes
                                            in
                                         let mk_tapp e ty_args =
                                           match ty_args with
                                           | [] -> e
                                           | uu____7477 ->
                                               let uu___63_7480 = e  in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (FStar_Extraction_ML_Syntax.MLE_TApp
                                                      (e, ty_args));
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   =
                                                   (uu___63_7480.FStar_Extraction_ML_Syntax.mlty);
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___63_7480.FStar_Extraction_ML_Syntax.loc)
                                               }
                                            in
                                         let head3 =
                                           match head_ml.FStar_Extraction_ML_Syntax.expr
                                           with
                                           | FStar_Extraction_ML_Syntax.MLE_Name
                                               uu____7484 ->
                                               let uu___64_7485 =
                                                 mk_tapp head_ml
                                                   prefixAsMLTypes
                                                  in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (uu___64_7485.FStar_Extraction_ML_Syntax.expr);
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   = t2;
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___64_7485.FStar_Extraction_ML_Syntax.loc)
                                               }
                                           | FStar_Extraction_ML_Syntax.MLE_Var
                                               uu____7486 ->
                                               let uu___64_7487 =
                                                 mk_tapp head_ml
                                                   prefixAsMLTypes
                                                  in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (uu___64_7487.FStar_Extraction_ML_Syntax.expr);
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   = t2;
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___64_7487.FStar_Extraction_ML_Syntax.loc)
                                               }
                                           | FStar_Extraction_ML_Syntax.MLE_App
                                               (head3,{
                                                        FStar_Extraction_ML_Syntax.expr
                                                          =
                                                          FStar_Extraction_ML_Syntax.MLE_Const
                                                          (FStar_Extraction_ML_Syntax.MLC_Unit
                                                          );
                                                        FStar_Extraction_ML_Syntax.mlty
                                                          = uu____7489;
                                                        FStar_Extraction_ML_Syntax.loc
                                                          = uu____7490;_}::[])
                                               ->
                                               FStar_All.pipe_right
                                                 (FStar_Extraction_ML_Syntax.MLE_App
                                                    ((let uu___65_7496 =
                                                        mk_tapp head3
                                                          prefixAsMLTypes
                                                         in
                                                      {
                                                        FStar_Extraction_ML_Syntax.expr
                                                          =
                                                          (uu___65_7496.FStar_Extraction_ML_Syntax.expr);
                                                        FStar_Extraction_ML_Syntax.mlty
                                                          =
                                                          (FStar_Extraction_ML_Syntax.MLTY_Fun
                                                             (FStar_Extraction_ML_Syntax.ml_unit_ty,
                                                               FStar_Extraction_ML_Syntax.E_PURE,
                                                               t2));
                                                        FStar_Extraction_ML_Syntax.loc
                                                          =
                                                          (uu___65_7496.FStar_Extraction_ML_Syntax.loc)
                                                      }),
                                                      [FStar_Extraction_ML_Syntax.ml_unit]))
                                                 (FStar_Extraction_ML_Syntax.with_ty
                                                    t2)
                                           | uu____7497 ->
                                               failwith
                                                 "Impossible: Unexpected head term"
                                            in
                                         (head3, t2, rest))
                                  else err_uninst g head2 (vars, t1) top
                               in
                            (match uu____7300 with
                             | (head_ml1,head_t,args1) ->
                                 (match args1 with
                                  | [] ->
                                      let uu____7558 =
                                        maybe_eta_data_and_project_record g
                                          qual head_t head_ml1
                                         in
                                      (uu____7558,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        head_t)
                                  | uu____7559 ->
                                      extract_app_maybe_projector qual
                                        head_ml1
                                        (FStar_Extraction_ML_Syntax.E_PURE,
                                          head_t) args1)))
                   | FStar_Syntax_Syntax.Tm_fvar uu____7568 ->
                       let uu____7569 =
                         let uu____7582 =
                           FStar_Extraction_ML_UEnv.lookup_term g head2  in
                         match uu____7582 with
                         | (FStar_Util.Inr (uu____7601,x1,x2,x3),q) ->
                             ((x1, x2, x3), q)
                         | uu____7646 -> failwith "FIXME Ty"  in
                       (match uu____7569 with
                        | ((head_ml,(vars,t1),inst_ok),qual) ->
                            let has_typ_apps =
                              match args with
                              | (a,uu____7696)::uu____7697 -> is_type g a
                              | uu____7716 -> false  in
                            let uu____7725 =
                              match vars with
                              | uu____7754::uu____7755 when
                                  (Prims.op_Negation has_typ_apps) && inst_ok
                                  -> (head_ml, t1, args)
                              | uu____7766 ->
                                  let n1 = FStar_List.length vars  in
                                  if n1 <= (FStar_List.length args)
                                  then
                                    let uu____7794 =
                                      FStar_Util.first_N n1 args  in
                                    (match uu____7794 with
                                     | (prefix1,rest) ->
                                         let prefixAsMLTypes =
                                           FStar_List.map
                                             (fun uu____7883  ->
                                                match uu____7883 with
                                                | (x,uu____7889) ->
                                                    term_as_mlty g x) prefix1
                                            in
                                         let t2 =
                                           instantiate (vars, t1)
                                             prefixAsMLTypes
                                            in
                                         let mk_tapp e ty_args =
                                           match ty_args with
                                           | [] -> e
                                           | uu____7902 ->
                                               let uu___63_7905 = e  in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (FStar_Extraction_ML_Syntax.MLE_TApp
                                                      (e, ty_args));
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   =
                                                   (uu___63_7905.FStar_Extraction_ML_Syntax.mlty);
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___63_7905.FStar_Extraction_ML_Syntax.loc)
                                               }
                                            in
                                         let head3 =
                                           match head_ml.FStar_Extraction_ML_Syntax.expr
                                           with
                                           | FStar_Extraction_ML_Syntax.MLE_Name
                                               uu____7909 ->
                                               let uu___64_7910 =
                                                 mk_tapp head_ml
                                                   prefixAsMLTypes
                                                  in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (uu___64_7910.FStar_Extraction_ML_Syntax.expr);
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   = t2;
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___64_7910.FStar_Extraction_ML_Syntax.loc)
                                               }
                                           | FStar_Extraction_ML_Syntax.MLE_Var
                                               uu____7911 ->
                                               let uu___64_7912 =
                                                 mk_tapp head_ml
                                                   prefixAsMLTypes
                                                  in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (uu___64_7912.FStar_Extraction_ML_Syntax.expr);
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   = t2;
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___64_7912.FStar_Extraction_ML_Syntax.loc)
                                               }
                                           | FStar_Extraction_ML_Syntax.MLE_App
                                               (head3,{
                                                        FStar_Extraction_ML_Syntax.expr
                                                          =
                                                          FStar_Extraction_ML_Syntax.MLE_Const
                                                          (FStar_Extraction_ML_Syntax.MLC_Unit
                                                          );
                                                        FStar_Extraction_ML_Syntax.mlty
                                                          = uu____7914;
                                                        FStar_Extraction_ML_Syntax.loc
                                                          = uu____7915;_}::[])
                                               ->
                                               FStar_All.pipe_right
                                                 (FStar_Extraction_ML_Syntax.MLE_App
                                                    ((let uu___65_7921 =
                                                        mk_tapp head3
                                                          prefixAsMLTypes
                                                         in
                                                      {
                                                        FStar_Extraction_ML_Syntax.expr
                                                          =
                                                          (uu___65_7921.FStar_Extraction_ML_Syntax.expr);
                                                        FStar_Extraction_ML_Syntax.mlty
                                                          =
                                                          (FStar_Extraction_ML_Syntax.MLTY_Fun
                                                             (FStar_Extraction_ML_Syntax.ml_unit_ty,
                                                               FStar_Extraction_ML_Syntax.E_PURE,
                                                               t2));
                                                        FStar_Extraction_ML_Syntax.loc
                                                          =
                                                          (uu___65_7921.FStar_Extraction_ML_Syntax.loc)
                                                      }),
                                                      [FStar_Extraction_ML_Syntax.ml_unit]))
                                                 (FStar_Extraction_ML_Syntax.with_ty
                                                    t2)
                                           | uu____7922 ->
                                               failwith
                                                 "Impossible: Unexpected head term"
                                            in
                                         (head3, t2, rest))
                                  else err_uninst g head2 (vars, t1) top
                               in
                            (match uu____7725 with
                             | (head_ml1,head_t,args1) ->
                                 (match args1 with
                                  | [] ->
                                      let uu____7983 =
                                        maybe_eta_data_and_project_record g
                                          qual head_t head_ml1
                                         in
                                      (uu____7983,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        head_t)
                                  | uu____7984 ->
                                      extract_app_maybe_projector qual
                                        head_ml1
                                        (FStar_Extraction_ML_Syntax.E_PURE,
                                          head_t) args1)))
                   | uu____7993 ->
                       let uu____7994 = term_as_mlexpr g head2  in
                       (match uu____7994 with
                        | (head3,f,t1) ->
                            extract_app_maybe_projector
                              FStar_Pervasives_Native.None head3 (f, t1) args)))
       | FStar_Syntax_Syntax.Tm_ascribed (e0,(tc,uu____8012),f) ->
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
           let uu____8079 = check_term_as_mlexpr g e0 f1 t1  in
           (match uu____8079 with | (e,t2) -> (e, f1, t2))
       | FStar_Syntax_Syntax.Tm_let ((is_rec,lbs),e') ->
           let top_level = FStar_Syntax_Syntax.is_top_level lbs  in
           let uu____8110 =
             if is_rec
             then FStar_Syntax_Subst.open_let_rec lbs e'
             else
               (let uu____8124 = FStar_Syntax_Syntax.is_top_level lbs  in
                if uu____8124
                then (lbs, e')
                else
                  (let lb = FStar_List.hd lbs  in
                   let x =
                     let uu____8138 =
                       FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                     FStar_Syntax_Syntax.freshen_bv uu____8138  in
                   let lb1 =
                     let uu___66_8140 = lb  in
                     {
                       FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                       FStar_Syntax_Syntax.lbunivs =
                         (uu___66_8140.FStar_Syntax_Syntax.lbunivs);
                       FStar_Syntax_Syntax.lbtyp =
                         (uu___66_8140.FStar_Syntax_Syntax.lbtyp);
                       FStar_Syntax_Syntax.lbeff =
                         (uu___66_8140.FStar_Syntax_Syntax.lbeff);
                       FStar_Syntax_Syntax.lbdef =
                         (uu___66_8140.FStar_Syntax_Syntax.lbdef);
                       FStar_Syntax_Syntax.lbattrs =
                         (uu___66_8140.FStar_Syntax_Syntax.lbattrs);
                       FStar_Syntax_Syntax.lbpos =
                         (uu___66_8140.FStar_Syntax_Syntax.lbpos)
                     }  in
                   let e'1 =
                     FStar_Syntax_Subst.subst
                       [FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x)] e'
                      in
                   ([lb1], e'1)))
              in
           (match uu____8110 with
            | (lbs1,e'1) ->
                let lbs2 =
                  if top_level
                  then
                    FStar_All.pipe_right lbs1
                      (FStar_List.map
                         (fun lb  ->
                            let tcenv =
                              let uu____8172 =
                                FStar_Ident.lid_of_path
                                  (FStar_List.append
                                     (FStar_Pervasives_Native.fst
                                        g.FStar_Extraction_ML_UEnv.currentModule)
                                     [FStar_Pervasives_Native.snd
                                        g.FStar_Extraction_ML_UEnv.currentModule])
                                  FStar_Range.dummyRange
                                 in
                              FStar_TypeChecker_Env.set_current_module
                                g.FStar_Extraction_ML_UEnv.tcenv uu____8172
                               in
                            FStar_Extraction_ML_UEnv.debug g
                              (fun uu____8179  ->
                                 FStar_Options.set_option "debug_level"
                                   (FStar_Options.List
                                      [FStar_Options.String "Norm";
                                      FStar_Options.String "Extraction"]));
                            (let lbdef =
                               let uu____8183 = FStar_Options.ml_ish ()  in
                               if uu____8183
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
                             let uu___67_8187 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___67_8187.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___67_8187.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___67_8187.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___67_8187.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___67_8187.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___67_8187.FStar_Syntax_Syntax.lbpos)
                             })))
                  else lbs1  in
                let maybe_generalize uu____8210 =
                  match uu____8210 with
                  | { FStar_Syntax_Syntax.lbname = lbname_;
                      FStar_Syntax_Syntax.lbunivs = uu____8230;
                      FStar_Syntax_Syntax.lbtyp = t1;
                      FStar_Syntax_Syntax.lbeff = lbeff;
                      FStar_Syntax_Syntax.lbdef = e;
                      FStar_Syntax_Syntax.lbattrs = uu____8234;
                      FStar_Syntax_Syntax.lbpos = uu____8235;_} ->
                      let f_e = effect_as_etag g lbeff  in
                      let t2 = FStar_Syntax_Subst.compress t1  in
                      let no_gen uu____8309 =
                        let expected_t = term_as_mlty g t2  in
                        (lbname_, f_e, (t2, ([], ([], expected_t))), false,
                          e)
                         in
                      if Prims.op_Negation top_level
                      then no_gen ()
                      else
                        (match t2.FStar_Syntax_Syntax.n with
                         | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                             let uu____8426 = FStar_List.hd bs  in
                             FStar_All.pipe_right uu____8426
                               (is_type_binder g)
                             ->
                             let uu____8439 =
                               FStar_Syntax_Subst.open_comp bs c  in
                             (match uu____8439 with
                              | (bs1,c1) ->
                                  let uu____8464 =
                                    let uu____8471 =
                                      FStar_Util.prefix_until
                                        (fun x  ->
                                           let uu____8507 =
                                             is_type_binder g x  in
                                           Prims.op_Negation uu____8507) bs1
                                       in
                                    match uu____8471 with
                                    | FStar_Pervasives_Native.None  ->
                                        (bs1,
                                          (FStar_Syntax_Util.comp_result c1))
                                    | FStar_Pervasives_Native.Some
                                        (bs2,b,rest) ->
                                        let uu____8595 =
                                          FStar_Syntax_Util.arrow (b :: rest)
                                            c1
                                           in
                                        (bs2, uu____8595)
                                     in
                                  (match uu____8464 with
                                   | (tbinders,tbody) ->
                                       let n_tbinders =
                                         FStar_List.length tbinders  in
                                       let e1 =
                                         let uu____8640 = normalize_abs e  in
                                         FStar_All.pipe_right uu____8640
                                           FStar_Syntax_Util.unmeta
                                          in
                                       (match e1.FStar_Syntax_Syntax.n with
                                        | FStar_Syntax_Syntax.Tm_abs
                                            (bs2,body,copt) ->
                                            let uu____8682 =
                                              FStar_Syntax_Subst.open_term
                                                bs2 body
                                               in
                                            (match uu____8682 with
                                             | (bs3,body1) ->
                                                 if
                                                   n_tbinders <=
                                                     (FStar_List.length bs3)
                                                 then
                                                   let uu____8735 =
                                                     FStar_Util.first_N
                                                       n_tbinders bs3
                                                      in
                                                   (match uu____8735 with
                                                    | (targs,rest_args) ->
                                                        let expected_source_ty
                                                          =
                                                          let s =
                                                            FStar_List.map2
                                                              (fun uu____8823
                                                                  ->
                                                                 fun
                                                                   uu____8824
                                                                    ->
                                                                   match 
                                                                    (uu____8823,
                                                                    uu____8824)
                                                                   with
                                                                   | 
                                                                   ((x,uu____8842),
                                                                    (y,uu____8844))
                                                                    ->
                                                                    let uu____8853
                                                                    =
                                                                    let uu____8860
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    y  in
                                                                    (x,
                                                                    uu____8860)
                                                                     in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____8853)
                                                              tbinders targs
                                                             in
                                                          FStar_Syntax_Subst.subst
                                                            s tbody
                                                           in
                                                        let env =
                                                          FStar_List.fold_left
                                                            (fun env  ->
                                                               fun uu____8871
                                                                  ->
                                                                 match uu____8871
                                                                 with
                                                                 | (a,uu____8877)
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
                                                          let uu____8886 =
                                                            FStar_All.pipe_right
                                                              targs
                                                              (FStar_List.map
                                                                 (fun
                                                                    uu____8904
                                                                     ->
                                                                    match uu____8904
                                                                    with
                                                                    | 
                                                                    (x,uu____8910)
                                                                    ->
                                                                    FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                                    x))
                                                             in
                                                          (uu____8886,
                                                            expected_t)
                                                           in
                                                        let add_unit =
                                                          match rest_args
                                                          with
                                                          | [] ->
                                                              let uu____8918
                                                                =
                                                                is_fstar_value
                                                                  body1
                                                                 in
                                                              Prims.op_Negation
                                                                uu____8918
                                                          | uu____8919 ->
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
                                            uu____8988 ->
                                            let env =
                                              FStar_List.fold_left
                                                (fun env  ->
                                                   fun uu____9005  ->
                                                     match uu____9005 with
                                                     | (a,uu____9011) ->
                                                         FStar_Extraction_ML_UEnv.extend_ty
                                                           env a
                                                           FStar_Pervasives_Native.None)
                                                g tbinders
                                               in
                                            let expected_t =
                                              term_as_mlty env tbody  in
                                            let polytype =
                                              let uu____9020 =
                                                FStar_All.pipe_right tbinders
                                                  (FStar_List.map
                                                     (fun uu____9032  ->
                                                        match uu____9032 with
                                                        | (x,uu____9038) ->
                                                            FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                              x))
                                                 in
                                              (uu____9020, expected_t)  in
                                            let args =
                                              FStar_All.pipe_right tbinders
                                                (FStar_List.map
                                                   (fun uu____9054  ->
                                                      match uu____9054 with
                                                      | (bv,uu____9060) ->
                                                          let uu____9061 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              bv
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____9061
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
                                            uu____9103 ->
                                            let env =
                                              FStar_List.fold_left
                                                (fun env  ->
                                                   fun uu____9114  ->
                                                     match uu____9114 with
                                                     | (a,uu____9120) ->
                                                         FStar_Extraction_ML_UEnv.extend_ty
                                                           env a
                                                           FStar_Pervasives_Native.None)
                                                g tbinders
                                               in
                                            let expected_t =
                                              term_as_mlty env tbody  in
                                            let polytype =
                                              let uu____9129 =
                                                FStar_All.pipe_right tbinders
                                                  (FStar_List.map
                                                     (fun uu____9141  ->
                                                        match uu____9141 with
                                                        | (x,uu____9147) ->
                                                            FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                              x))
                                                 in
                                              (uu____9129, expected_t)  in
                                            let args =
                                              FStar_All.pipe_right tbinders
                                                (FStar_List.map
                                                   (fun uu____9163  ->
                                                      match uu____9163 with
                                                      | (bv,uu____9169) ->
                                                          let uu____9170 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              bv
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____9170
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
                                            uu____9212 ->
                                            let env =
                                              FStar_List.fold_left
                                                (fun env  ->
                                                   fun uu____9223  ->
                                                     match uu____9223 with
                                                     | (a,uu____9229) ->
                                                         FStar_Extraction_ML_UEnv.extend_ty
                                                           env a
                                                           FStar_Pervasives_Native.None)
                                                g tbinders
                                               in
                                            let expected_t =
                                              term_as_mlty env tbody  in
                                            let polytype =
                                              let uu____9238 =
                                                FStar_All.pipe_right tbinders
                                                  (FStar_List.map
                                                     (fun uu____9250  ->
                                                        match uu____9250 with
                                                        | (x,uu____9256) ->
                                                            FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                              x))
                                                 in
                                              (uu____9238, expected_t)  in
                                            let args =
                                              FStar_All.pipe_right tbinders
                                                (FStar_List.map
                                                   (fun uu____9272  ->
                                                      match uu____9272 with
                                                      | (bv,uu____9278) ->
                                                          let uu____9279 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              bv
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____9279
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
                                        | uu____9321 ->
                                            err_value_restriction e1)))
                         | uu____9340 -> no_gen ())
                   in
                let check_lb env uu____9383 =
                  match uu____9383 with
                  | (nm,(lbname,f,(t1,(targs,polytype)),add_unit,e)) ->
                      let env1 =
                        FStar_List.fold_left
                          (fun env1  ->
                             fun uu____9518  ->
                               match uu____9518 with
                               | (a,uu____9524) ->
                                   FStar_Extraction_ML_UEnv.extend_ty env1 a
                                     FStar_Pervasives_Native.None) env targs
                         in
                      let expected_t = FStar_Pervasives_Native.snd polytype
                         in
                      let uu____9526 =
                        check_term_as_mlexpr env1 e f expected_t  in
                      (match uu____9526 with
                       | (e1,uu____9536) ->
                           let f1 = maybe_downgrade_eff env1 f expected_t  in
                           (f1,
                             {
                               FStar_Extraction_ML_Syntax.mllb_name = nm;
                               FStar_Extraction_ML_Syntax.mllb_tysc =
                                 (FStar_Pervasives_Native.Some polytype);
                               FStar_Extraction_ML_Syntax.mllb_add_unit =
                                 add_unit;
                               FStar_Extraction_ML_Syntax.mllb_def = e1;
                               FStar_Extraction_ML_Syntax.mllb_meta = [];
                               FStar_Extraction_ML_Syntax.print_typ = true
                             }))
                   in
                let lbs3 =
                  FStar_All.pipe_right lbs2 (FStar_List.map maybe_generalize)
                   in
                let uu____9603 =
                  FStar_List.fold_right
                    (fun lb  ->
                       fun uu____9694  ->
                         match uu____9694 with
                         | (env,lbs4) ->
                             let uu____9819 = lb  in
                             (match uu____9819 with
                              | (lbname,uu____9867,(t1,(uu____9869,polytype)),add_unit,uu____9872)
                                  ->
                                  let uu____9885 =
                                    FStar_Extraction_ML_UEnv.extend_lb env
                                      lbname t1 polytype add_unit true
                                     in
                                  (match uu____9885 with
                                   | (env1,nm) -> (env1, ((nm, lb) :: lbs4)))))
                    lbs3 (g, [])
                   in
                (match uu____9603 with
                 | (env_body,lbs4) ->
                     let env_def = if is_rec then env_body else g  in
                     let lbs5 =
                       FStar_All.pipe_right lbs4
                         (FStar_List.map (check_lb env_def))
                        in
                     let e'_rng = e'1.FStar_Syntax_Syntax.pos  in
                     let uu____10162 = term_as_mlexpr env_body e'1  in
                     (match uu____10162 with
                      | (e'2,f',t') ->
                          let f =
                            let uu____10179 =
                              let uu____10182 =
                                FStar_List.map FStar_Pervasives_Native.fst
                                  lbs5
                                 in
                              f' :: uu____10182  in
                            FStar_Extraction_ML_Util.join_l e'_rng
                              uu____10179
                             in
                          let is_rec1 =
                            if is_rec = true
                            then FStar_Extraction_ML_Syntax.Rec
                            else FStar_Extraction_ML_Syntax.NonRec  in
                          let uu____10191 =
                            let uu____10192 =
                              let uu____10193 =
                                let uu____10194 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    lbs5
                                   in
                                (is_rec1, uu____10194)  in
                              mk_MLE_Let top_level uu____10193 e'2  in
                            let uu____10203 =
                              FStar_Extraction_ML_Util.mlloc_of_range
                                t.FStar_Syntax_Syntax.pos
                               in
                            FStar_Extraction_ML_Syntax.with_ty_loc t'
                              uu____10192 uu____10203
                             in
                          (uu____10191, f, t'))))
       | FStar_Syntax_Syntax.Tm_match (scrutinee,pats) ->
           let uu____10242 = term_as_mlexpr g scrutinee  in
           (match uu____10242 with
            | (e,f_e,t_e) ->
                let uu____10258 = check_pats_for_ite pats  in
                (match uu____10258 with
                 | (b,then_e,else_e) ->
                     let no_lift x t1 = x  in
                     if b
                     then
                       (match (then_e, else_e) with
                        | (FStar_Pervasives_Native.Some
                           then_e1,FStar_Pervasives_Native.Some else_e1) ->
                            let uu____10315 = term_as_mlexpr g then_e1  in
                            (match uu____10315 with
                             | (then_mle,f_then,t_then) ->
                                 let uu____10331 = term_as_mlexpr g else_e1
                                    in
                                 (match uu____10331 with
                                  | (else_mle,f_else,t_else) ->
                                      let uu____10347 =
                                        let uu____10356 =
                                          type_leq g t_then t_else  in
                                        if uu____10356
                                        then (t_else, no_lift)
                                        else
                                          (let uu____10370 =
                                             type_leq g t_else t_then  in
                                           if uu____10370
                                           then (t_then, no_lift)
                                           else
                                             (FStar_Extraction_ML_Syntax.MLTY_Top,
                                               FStar_Extraction_ML_Syntax.apply_obj_repr))
                                         in
                                      (match uu____10347 with
                                       | (t_branch,maybe_lift1) ->
                                           let uu____10404 =
                                             let uu____10405 =
                                               let uu____10406 =
                                                 let uu____10415 =
                                                   maybe_lift1 then_mle
                                                     t_then
                                                    in
                                                 let uu____10416 =
                                                   let uu____10419 =
                                                     maybe_lift1 else_mle
                                                       t_else
                                                      in
                                                   FStar_Pervasives_Native.Some
                                                     uu____10419
                                                    in
                                                 (e, uu____10415,
                                                   uu____10416)
                                                  in
                                               FStar_Extraction_ML_Syntax.MLE_If
                                                 uu____10406
                                                in
                                             FStar_All.pipe_left
                                               (FStar_Extraction_ML_Syntax.with_ty
                                                  t_branch) uu____10405
                                              in
                                           let uu____10422 =
                                             FStar_Extraction_ML_Util.join
                                               then_e1.FStar_Syntax_Syntax.pos
                                               f_then f_else
                                              in
                                           (uu____10404, uu____10422,
                                             t_branch))))
                        | uu____10423 ->
                            failwith
                              "ITE pats matched but then and else expressions not found?")
                     else
                       (let uu____10439 =
                          FStar_All.pipe_right pats
                            (FStar_Util.fold_map
                               (fun compat  ->
                                  fun br  ->
                                    let uu____10548 =
                                      FStar_Syntax_Subst.open_branch br  in
                                    match uu____10548 with
                                    | (pat,when_opt,branch1) ->
                                        let uu____10592 =
                                          extract_pat g pat t_e
                                            term_as_mlexpr
                                           in
                                        (match uu____10592 with
                                         | (env,p,pat_t_compat) ->
                                             let uu____10650 =
                                               match when_opt with
                                               | FStar_Pervasives_Native.None
                                                    ->
                                                   (FStar_Pervasives_Native.None,
                                                     FStar_Extraction_ML_Syntax.E_PURE)
                                               | FStar_Pervasives_Native.Some
                                                   w ->
                                                   let uu____10672 =
                                                     term_as_mlexpr env w  in
                                                   (match uu____10672 with
                                                    | (w1,f_w,t_w) ->
                                                        let w2 =
                                                          maybe_coerce env w1
                                                            t_w
                                                            FStar_Extraction_ML_Syntax.ml_bool_ty
                                                           in
                                                        ((FStar_Pervasives_Native.Some
                                                            w2), f_w))
                                                in
                                             (match uu____10650 with
                                              | (when_opt1,f_when) ->
                                                  let uu____10721 =
                                                    term_as_mlexpr env
                                                      branch1
                                                     in
                                                  (match uu____10721 with
                                                   | (mlbranch,f_branch,t_branch)
                                                       ->
                                                       let uu____10755 =
                                                         FStar_All.pipe_right
                                                           p
                                                           (FStar_List.map
                                                              (fun
                                                                 uu____10832 
                                                                 ->
                                                                 match uu____10832
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
                                                         uu____10755)))))
                               true)
                           in
                        match uu____10439 with
                        | (pat_t_compat,mlbranches) ->
                            let mlbranches1 = FStar_List.flatten mlbranches
                               in
                            let e1 =
                              if pat_t_compat
                              then e
                              else
                                (FStar_Extraction_ML_UEnv.debug g
                                   (fun uu____10997  ->
                                      let uu____10998 =
                                        FStar_Extraction_ML_Code.string_of_mlexpr
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          e
                                         in
                                      let uu____10999 =
                                        FStar_Extraction_ML_Code.string_of_mlty
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          t_e
                                         in
                                      FStar_Util.print2
                                        "Coercing scrutinee %s from type %s because pattern type is incompatible\n"
                                        uu____10998 uu____10999);
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty t_e)
                                   (FStar_Extraction_ML_Syntax.MLE_Coerce
                                      (e, t_e,
                                        FStar_Extraction_ML_Syntax.MLTY_Top)))
                               in
                            (match mlbranches1 with
                             | [] ->
                                 let uu____11024 =
                                   let uu____11033 =
                                     let uu____11050 =
                                       FStar_Syntax_Syntax.lid_as_fv
                                         FStar_Parser_Const.failwith_lid
                                         FStar_Syntax_Syntax.Delta_constant
                                         FStar_Pervasives_Native.None
                                        in
                                     FStar_Extraction_ML_UEnv.lookup_fv g
                                       uu____11050
                                      in
                                   FStar_All.pipe_left FStar_Util.right
                                     uu____11033
                                    in
                                 (match uu____11024 with
                                  | (uu____11093,fw,uu____11095,uu____11096)
                                      ->
                                      let uu____11097 =
                                        let uu____11098 =
                                          let uu____11099 =
                                            let uu____11106 =
                                              let uu____11109 =
                                                FStar_All.pipe_left
                                                  (FStar_Extraction_ML_Syntax.with_ty
                                                     FStar_Extraction_ML_Syntax.ml_string_ty)
                                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                                     (FStar_Extraction_ML_Syntax.MLC_String
                                                        "unreachable"))
                                                 in
                                              [uu____11109]  in
                                            (fw, uu____11106)  in
                                          FStar_Extraction_ML_Syntax.MLE_App
                                            uu____11099
                                           in
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             FStar_Extraction_ML_Syntax.ml_int_ty)
                                          uu____11098
                                         in
                                      (uu____11097,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        FStar_Extraction_ML_Syntax.ml_int_ty))
                             | (uu____11112,uu____11113,(uu____11114,f_first,t_first))::rest
                                 ->
                                 let uu____11174 =
                                   FStar_List.fold_left
                                     (fun uu____11216  ->
                                        fun uu____11217  ->
                                          match (uu____11216, uu____11217)
                                          with
                                          | ((topt,f),(uu____11274,uu____11275,
                                                       (uu____11276,f_branch,t_branch)))
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
                                                    let uu____11332 =
                                                      type_leq g t1 t_branch
                                                       in
                                                    if uu____11332
                                                    then
                                                      FStar_Pervasives_Native.Some
                                                        t_branch
                                                    else
                                                      (let uu____11336 =
                                                         type_leq g t_branch
                                                           t1
                                                          in
                                                       if uu____11336
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
                                 (match uu____11174 with
                                  | (topt,f_match) ->
                                      let mlbranches2 =
                                        FStar_All.pipe_right mlbranches1
                                          (FStar_List.map
                                             (fun uu____11431  ->
                                                match uu____11431 with
                                                | (p,(wopt,uu____11460),
                                                   (b1,uu____11462,t1)) ->
                                                    let b2 =
                                                      match topt with
                                                      | FStar_Pervasives_Native.None
                                                           ->
                                                          FStar_Extraction_ML_Syntax.apply_obj_repr
                                                            b1 t1
                                                      | FStar_Pervasives_Native.Some
                                                          uu____11481 -> b1
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
                                      let uu____11486 =
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             t_match)
                                          (FStar_Extraction_ML_Syntax.MLE_Match
                                             (e1, mlbranches2))
                                         in
                                      (uu____11486, f_match, t_match)))))))

let (ind_discriminator_body :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlmodule1)
  =
  fun env  ->
    fun discName  ->
      fun constrName  ->
        let uu____11506 =
          let uu____11511 =
            FStar_TypeChecker_Env.lookup_lid
              env.FStar_Extraction_ML_UEnv.tcenv discName
             in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____11511  in
        match uu____11506 with
        | (uu____11536,fstar_disc_type) ->
            let wildcards =
              let uu____11545 =
                let uu____11546 = FStar_Syntax_Subst.compress fstar_disc_type
                   in
                uu____11546.FStar_Syntax_Syntax.n  in
              match uu____11545 with
              | FStar_Syntax_Syntax.Tm_arrow (binders,uu____11556) ->
                  let uu____11573 =
                    FStar_All.pipe_right binders
                      (FStar_List.filter
                         (fun uu___60_11605  ->
                            match uu___60_11605 with
                            | (uu____11612,FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____11613)) ->
                                true
                            | uu____11616 -> false))
                     in
                  FStar_All.pipe_right uu____11573
                    (FStar_List.map
                       (fun uu____11649  ->
                          let uu____11656 = fresh "_"  in
                          (uu____11656, FStar_Extraction_ML_Syntax.MLTY_Top)))
              | uu____11657 -> failwith "Discriminator must be a function"
               in
            let mlid = fresh "_discr_"  in
            let targ = FStar_Extraction_ML_Syntax.MLTY_Top  in
            let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top  in
            let discrBody =
              let uu____11668 =
                let uu____11669 =
                  let uu____11680 =
                    let uu____11681 =
                      let uu____11682 =
                        let uu____11697 =
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty targ)
                            (FStar_Extraction_ML_Syntax.MLE_Name ([], mlid))
                           in
                        let uu____11700 =
                          let uu____11711 =
                            let uu____11720 =
                              let uu____11721 =
                                let uu____11728 =
                                  FStar_Extraction_ML_Syntax.mlpath_of_lident
                                    constrName
                                   in
                                (uu____11728,
                                  [FStar_Extraction_ML_Syntax.MLP_Wild])
                                 in
                              FStar_Extraction_ML_Syntax.MLP_CTor uu____11721
                               in
                            let uu____11731 =
                              FStar_All.pipe_left
                                (FStar_Extraction_ML_Syntax.with_ty
                                   FStar_Extraction_ML_Syntax.ml_bool_ty)
                                (FStar_Extraction_ML_Syntax.MLE_Const
                                   (FStar_Extraction_ML_Syntax.MLC_Bool true))
                               in
                            (uu____11720, FStar_Pervasives_Native.None,
                              uu____11731)
                             in
                          let uu____11734 =
                            let uu____11745 =
                              let uu____11754 =
                                FStar_All.pipe_left
                                  (FStar_Extraction_ML_Syntax.with_ty
                                     FStar_Extraction_ML_Syntax.ml_bool_ty)
                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                     (FStar_Extraction_ML_Syntax.MLC_Bool
                                        false))
                                 in
                              (FStar_Extraction_ML_Syntax.MLP_Wild,
                                FStar_Pervasives_Native.None, uu____11754)
                               in
                            [uu____11745]  in
                          uu____11711 :: uu____11734  in
                        (uu____11697, uu____11700)  in
                      FStar_Extraction_ML_Syntax.MLE_Match uu____11682  in
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.ml_bool_ty) uu____11681
                     in
                  ((FStar_List.append wildcards [(mlid, targ)]), uu____11680)
                   in
                FStar_Extraction_ML_Syntax.MLE_Fun uu____11669  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty disc_ty) uu____11668
               in
            let uu____11809 =
              let uu____11810 =
                let uu____11813 =
                  let uu____11814 =
                    FStar_Extraction_ML_UEnv.convIdent
                      discName.FStar_Ident.ident
                     in
                  {
                    FStar_Extraction_ML_Syntax.mllb_name = uu____11814;
                    FStar_Extraction_ML_Syntax.mllb_tysc =
                      FStar_Pervasives_Native.None;
                    FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                    FStar_Extraction_ML_Syntax.mllb_def = discrBody;
                    FStar_Extraction_ML_Syntax.mllb_meta = [];
                    FStar_Extraction_ML_Syntax.print_typ = false
                  }  in
                [uu____11813]  in
              (FStar_Extraction_ML_Syntax.NonRec, uu____11810)  in
            FStar_Extraction_ML_Syntax.MLM_Let uu____11809
  