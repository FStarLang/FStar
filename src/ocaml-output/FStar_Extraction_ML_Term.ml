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
  'Auu____78 .
    FStar_Ident.ident Prims.list ->
      'Auu____78 Prims.list ->
        (Prims.string,'Auu____78) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun fs  ->
    fun vs  ->
      FStar_List.map2 (fun f  -> fun e  -> ((f.FStar_Ident.idText), e)) fs vs
  
let fail :
  'Auu____117 .
    FStar_Range.range ->
      (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2 ->
        'Auu____117
  = fun r  -> fun err  -> FStar_Errors.raise_error err r 
let err_uninst :
  'Auu____146 .
    FStar_Extraction_ML_UEnv.env ->
      FStar_Syntax_Syntax.term ->
        (Prims.string Prims.list,FStar_Extraction_ML_Syntax.mlty)
          FStar_Pervasives_Native.tuple2 ->
          FStar_Syntax_Syntax.term -> 'Auu____146
  =
  fun env  ->
    fun t  ->
      fun uu____171  ->
        fun app  ->
          match uu____171 with
          | (vars,ty) ->
              let uu____185 =
                let uu____190 =
                  let uu____191 = FStar_Syntax_Print.term_to_string t  in
                  let uu____192 =
                    FStar_All.pipe_right vars (FStar_String.concat ", ")  in
                  let uu____195 =
                    FStar_Extraction_ML_Code.string_of_mlty
                      env.FStar_Extraction_ML_UEnv.currentModule ty
                     in
                  let uu____196 = FStar_Syntax_Print.term_to_string app  in
                  FStar_Util.format4
                    "Variable %s has a polymorphic type (forall %s. %s); expected it to be fully instantiated, but got %s"
                    uu____191 uu____192 uu____195 uu____196
                   in
                (FStar_Errors.Fatal_Uninstantiated, uu____190)  in
              fail t.FStar_Syntax_Syntax.pos uu____185
  
let err_ill_typed_application :
  'Auu____209 'Auu____210 .
    FStar_Extraction_ML_UEnv.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term,'Auu____209) FStar_Pervasives_Native.tuple2
          Prims.list -> FStar_Extraction_ML_Syntax.mlty -> 'Auu____210
  =
  fun env  ->
    fun t  ->
      fun args  ->
        fun ty  ->
          let uu____243 =
            let uu____248 =
              let uu____249 = FStar_Syntax_Print.term_to_string t  in
              let uu____250 =
                let uu____251 =
                  FStar_All.pipe_right args
                    (FStar_List.map
                       (fun uu____269  ->
                          match uu____269 with
                          | (x,uu____275) ->
                              FStar_Syntax_Print.term_to_string x))
                   in
                FStar_All.pipe_right uu____251 (FStar_String.concat " ")  in
              let uu____278 =
                FStar_Extraction_ML_Code.string_of_mlty
                  env.FStar_Extraction_ML_UEnv.currentModule ty
                 in
              FStar_Util.format3
                "Ill-typed application: application is %s \n remaining args are %s\nml type of head is %s\n"
                uu____249 uu____250 uu____278
               in
            (FStar_Errors.Fatal_IllTyped, uu____248)  in
          fail t.FStar_Syntax_Syntax.pos uu____243
  
let err_value_restriction :
  'Auu____283 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> 'Auu____283
  =
  fun t  ->
    let uu____293 =
      let uu____298 =
        let uu____299 = FStar_Syntax_Print.tag_of_term t  in
        let uu____300 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format2
          "Refusing to generalize because of the value restriction: (%s) %s"
          uu____299 uu____300
         in
      (FStar_Errors.Fatal_ValueRestriction, uu____298)  in
    fail t.FStar_Syntax_Syntax.pos uu____293
  
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
            let uu____330 =
              let uu____335 =
                let uu____336 = FStar_Syntax_Print.term_to_string t  in
                let uu____337 =
                  FStar_Extraction_ML_Code.string_of_mlty
                    env.FStar_Extraction_ML_UEnv.currentModule ty
                   in
                let uu____338 = FStar_Extraction_ML_Util.eff_to_string f0  in
                let uu____339 = FStar_Extraction_ML_Util.eff_to_string f1  in
                FStar_Util.format4
                  "for expression %s of type %s, Expected effect %s; got effect %s"
                  uu____336 uu____337 uu____338 uu____339
                 in
              (FStar_Errors.Warning_ExtractionUnexpectedEffect, uu____335)
               in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____330
  
let (effect_as_etag :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Ident.lident -> FStar_Extraction_ML_Syntax.e_tag)
  =
  let cache = FStar_Util.smap_create (Prims.parse_int "20")  in
  let rec delta_norm_eff g l =
    let uu____360 = FStar_Util.smap_try_find cache l.FStar_Ident.str  in
    match uu____360 with
    | FStar_Pervasives_Native.Some l1 -> l1
    | FStar_Pervasives_Native.None  ->
        let res =
          let uu____365 =
            FStar_TypeChecker_Env.lookup_effect_abbrev
              g.FStar_Extraction_ML_UEnv.tcenv [FStar_Syntax_Syntax.U_zero] l
             in
          match uu____365 with
          | FStar_Pervasives_Native.None  -> l
          | FStar_Pervasives_Native.Some (uu____376,c) ->
              delta_norm_eff g (FStar_Syntax_Util.comp_effect_name c)
           in
        let uu____382 = FStar_Util.smap_add cache l.FStar_Ident.str res  in
        res
     in
  fun g  ->
    fun l  ->
      let l1 = delta_norm_eff g l  in
      let uu____386 =
        FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid  in
      if uu____386
      then FStar_Extraction_ML_Syntax.E_PURE
      else
        (let uu____388 =
           FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GHOST_lid  in
         if uu____388
         then FStar_Extraction_ML_Syntax.E_GHOST
         else
           (let ed_opt =
              FStar_TypeChecker_Env.effect_decl_opt
                g.FStar_Extraction_ML_UEnv.tcenv l1
               in
            match ed_opt with
            | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                let uu____411 =
                  FStar_All.pipe_right qualifiers
                    (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                   in
                if uu____411
                then FStar_Extraction_ML_Syntax.E_PURE
                else FStar_Extraction_ML_Syntax.E_IMPURE
            | FStar_Pervasives_Native.None  ->
                FStar_Extraction_ML_Syntax.E_IMPURE))
  
let rec (is_arity :
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t  in
      let uu____432 =
        let uu____433 = FStar_Syntax_Subst.compress t1  in
        uu____433.FStar_Syntax_Syntax.n  in
      match uu____432 with
      | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____436 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_ascribed uu____461 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_meta uu____488 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____496 = FStar_Syntax_Util.unfold_lazy i  in
          is_arity env uu____496
      | FStar_Syntax_Syntax.Tm_uvar uu____497 -> false
      | FStar_Syntax_Syntax.Tm_constant uu____514 -> false
      | FStar_Syntax_Syntax.Tm_name uu____515 -> false
      | FStar_Syntax_Syntax.Tm_quoted uu____516 -> false
      | FStar_Syntax_Syntax.Tm_bvar uu____523 -> false
      | FStar_Syntax_Syntax.Tm_type uu____524 -> true
      | FStar_Syntax_Syntax.Tm_arrow (uu____525,c) ->
          is_arity env (FStar_Syntax_Util.comp_result c)
      | FStar_Syntax_Syntax.Tm_fvar uu____543 ->
          let t2 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Normalize.AllowUnboundUniverses;
              FStar_TypeChecker_Normalize.EraseUniverses;
              FStar_TypeChecker_Normalize.UnfoldUntil
                FStar_Syntax_Syntax.Delta_constant]
              env.FStar_Extraction_ML_UEnv.tcenv t1
             in
          let uu____545 =
            let uu____546 = FStar_Syntax_Subst.compress t2  in
            uu____546.FStar_Syntax_Syntax.n  in
          (match uu____545 with
           | FStar_Syntax_Syntax.Tm_fvar uu____549 -> false
           | uu____550 -> is_arity env t2)
      | FStar_Syntax_Syntax.Tm_app uu____551 ->
          let uu____566 = FStar_Syntax_Util.head_and_args t1  in
          (match uu____566 with | (head1,uu____582) -> is_arity env head1)
      | FStar_Syntax_Syntax.Tm_uinst (head1,uu____604) -> is_arity env head1
      | FStar_Syntax_Syntax.Tm_refine (x,uu____610) ->
          is_arity env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_abs (uu____615,body,uu____617) ->
          is_arity env body
      | FStar_Syntax_Syntax.Tm_let (uu____638,body) -> is_arity env body
      | FStar_Syntax_Syntax.Tm_match (uu____656,branches) ->
          (match branches with
           | (uu____694,uu____695,e)::uu____697 -> is_arity env e
           | uu____744 -> false)
  
let rec (is_type_aux :
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____772 ->
          let uu____797 =
            let uu____798 = FStar_Syntax_Print.tag_of_term t1  in
            FStar_Util.format1 "Impossible: %s" uu____798  in
          failwith uu____797
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____799 =
            let uu____800 = FStar_Syntax_Print.tag_of_term t1  in
            FStar_Util.format1 "Impossible: %s" uu____800  in
          failwith uu____799
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____802 = FStar_Syntax_Util.unfold_lazy i  in
          is_type_aux env uu____802
      | FStar_Syntax_Syntax.Tm_constant uu____803 -> false
      | FStar_Syntax_Syntax.Tm_type uu____804 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____805 -> true
      | FStar_Syntax_Syntax.Tm_arrow uu____812 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.failwith_lid ->
          false
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Extraction_ML_UEnv.is_type_name env fv
      | FStar_Syntax_Syntax.Tm_uvar (uu____827,t2) -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_bvar
          { FStar_Syntax_Syntax.ppname = uu____853;
            FStar_Syntax_Syntax.index = uu____854;
            FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_name
          { FStar_Syntax_Syntax.ppname = uu____858;
            FStar_Syntax_Syntax.index = uu____859;
            FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____864,uu____865) ->
          is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____907) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____914) ->
          let uu____935 = FStar_Syntax_Subst.open_term bs body  in
          (match uu____935 with | (uu____940,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
          let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
          let uu____957 =
            let uu____962 =
              let uu____963 = FStar_Syntax_Syntax.mk_binder x  in [uu____963]
               in
            FStar_Syntax_Subst.open_term uu____962 body  in
          (match uu____957 with | (uu____964,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_let ((uu____966,lbs),body) ->
          let uu____983 = FStar_Syntax_Subst.open_let_rec lbs body  in
          (match uu____983 with | (uu____990,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_match (uu____996,branches) ->
          (match branches with
           | b::uu____1035 ->
               let uu____1080 = FStar_Syntax_Subst.open_branch b  in
               (match uu____1080 with
                | (uu____1081,uu____1082,e) -> is_type_aux env e)
           | uu____1100 -> false)
      | FStar_Syntax_Syntax.Tm_quoted uu____1117 -> false
      | FStar_Syntax_Syntax.Tm_meta (t2,uu____1125) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_app (head1,uu____1131) ->
          is_type_aux env head1
  
let (is_type :
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____1162 =
        FStar_Extraction_ML_UEnv.debug env
          (fun uu____1166  ->
             let uu____1167 = FStar_Syntax_Print.tag_of_term t  in
             let uu____1168 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print2 "checking is_type (%s) %s\n" uu____1167
               uu____1168)
         in
      let b = is_type_aux env t  in
      let uu____1170 =
        FStar_Extraction_ML_UEnv.debug env
          (fun uu____1174  ->
             if b
             then
               let uu____1175 = FStar_Syntax_Print.term_to_string t  in
               let uu____1176 = FStar_Syntax_Print.tag_of_term t  in
               FStar_Util.print2 "is_type %s (%s)\n" uu____1175 uu____1176
             else
               (let uu____1178 = FStar_Syntax_Print.term_to_string t  in
                let uu____1179 = FStar_Syntax_Print.tag_of_term t  in
                FStar_Util.print2 "not a type %s (%s)\n" uu____1178
                  uu____1179))
         in
      b
  
let is_type_binder :
  'Auu____1186 .
    FStar_Extraction_ML_UEnv.env ->
      (FStar_Syntax_Syntax.bv,'Auu____1186) FStar_Pervasives_Native.tuple2 ->
        Prims.bool
  =
  fun env  ->
    fun x  ->
      is_arity env (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
  
let (is_constructor : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1210 =
      let uu____1211 = FStar_Syntax_Subst.compress t  in
      uu____1211.FStar_Syntax_Syntax.n  in
    match uu____1210 with
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____1214;
          FStar_Syntax_Syntax.fv_delta = uu____1215;
          FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
            (FStar_Syntax_Syntax.Data_ctor );_}
        -> true
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____1216;
          FStar_Syntax_Syntax.fv_delta = uu____1217;
          FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
            (FStar_Syntax_Syntax.Record_ctor uu____1218);_}
        -> true
    | uu____1225 -> false
  
let rec (is_fstar_value : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1231 =
      let uu____1232 = FStar_Syntax_Subst.compress t  in
      uu____1232.FStar_Syntax_Syntax.n  in
    match uu____1231 with
    | FStar_Syntax_Syntax.Tm_constant uu____1235 -> true
    | FStar_Syntax_Syntax.Tm_bvar uu____1236 -> true
    | FStar_Syntax_Syntax.Tm_fvar uu____1237 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____1238 -> true
    | FStar_Syntax_Syntax.Tm_app (head1,args) ->
        let uu____1277 = is_constructor head1  in
        if uu____1277
        then
          FStar_All.pipe_right args
            (FStar_List.for_all
               (fun uu____1293  ->
                  match uu____1293 with
                  | (te,uu____1299) -> is_fstar_value te))
        else false
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____1302) -> is_fstar_value t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____1308,uu____1309) ->
        is_fstar_value t1
    | uu____1350 -> false
  
let rec (is_ml_value : FStar_Extraction_ML_Syntax.mlexpr -> Prims.bool) =
  fun e  ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_Const uu____1356 -> true
    | FStar_Extraction_ML_Syntax.MLE_Var uu____1357 -> true
    | FStar_Extraction_ML_Syntax.MLE_Name uu____1358 -> true
    | FStar_Extraction_ML_Syntax.MLE_Fun uu____1359 -> true
    | FStar_Extraction_ML_Syntax.MLE_CTor (uu____1370,exps) ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Tuple exps ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Record (uu____1379,fields) ->
        FStar_Util.for_all
          (fun uu____1404  ->
             match uu____1404 with | (uu____1409,e1) -> is_ml_value e1)
          fields
    | FStar_Extraction_ML_Syntax.MLE_TApp (h,uu____1412) -> is_ml_value h
    | uu____1417 -> false
  
let (fresh : Prims.string -> Prims.string) =
  let c = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun x  ->
    let uu____1426 = FStar_Util.incr c  in
    let uu____1460 =
      let uu____1461 = FStar_ST.op_Bang c  in
      FStar_Util.string_of_int uu____1461  in
    Prims.strcat x uu____1460
  
let (normalize_abs : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t0  ->
    let rec aux bs t copt =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_abs (bs',body,copt1) ->
          aux (FStar_List.append bs bs') body copt1
      | uu____1569 ->
          let e' = FStar_Syntax_Util.unascribe t1  in
          let uu____1571 = FStar_Syntax_Util.is_fun e'  in
          if uu____1571
          then aux bs e' copt
          else FStar_Syntax_Util.abs bs e' copt
       in
    aux [] t0 FStar_Pervasives_Native.None
  
let (unit_binder : FStar_Syntax_Syntax.binder) =
  let uu____1577 =
    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
      FStar_Syntax_Syntax.t_unit
     in
  FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____1577 
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
      (let uu____1657 = FStar_List.hd l  in
       match uu____1657 with
       | (p1,w1,e1) ->
           let uu____1691 =
             let uu____1700 = FStar_List.tl l  in FStar_List.hd uu____1700
              in
           (match uu____1691 with
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
                 | uu____1774 -> def)))
  
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
      let uu____1811 = FStar_Extraction_ML_Util.doms_and_cod t  in
      match uu____1811 with
      | (ts,r) ->
          if ts = []
          then e
          else
            (let vs = FStar_List.map (fun uu____1831  -> fresh "a") ts  in
             let vs_ts = FStar_List.zip vs ts  in
             let vs_es =
               let uu____1842 = FStar_List.zip vs ts  in
               FStar_List.map
                 (fun uu____1856  ->
                    match uu____1856 with
                    | (v1,t1) ->
                        FStar_Extraction_ML_Syntax.with_ty t1
                          (FStar_Extraction_ML_Syntax.MLE_Var v1)) uu____1842
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
      let uu____1882 =
        (FStar_Options.ml_no_eta_expand_coertions ()) ||
          (let uu____1884 = FStar_Options.codegen ()  in
           uu____1884 = (FStar_Pervasives_Native.Some FStar_Options.Kremlin))
         in
      if uu____1882 then e else eta_expand expect e
  
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
          let uu____1911 =
            type_leq_c g (FStar_Pervasives_Native.Some e) ty1 expect  in
          match uu____1911 with
          | (true ,FStar_Pervasives_Native.Some e') -> e'
          | uu____1921 ->
              let uu____1928 =
                FStar_Extraction_ML_UEnv.debug g
                  (fun uu____1933  ->
                     let uu____1934 =
                       FStar_Extraction_ML_Code.string_of_mlexpr
                         g.FStar_Extraction_ML_UEnv.currentModule e
                        in
                     let uu____1935 =
                       FStar_Extraction_ML_Code.string_of_mlty
                         g.FStar_Extraction_ML_UEnv.currentModule ty1
                        in
                     let uu____1936 =
                       FStar_Extraction_ML_Code.string_of_mlty
                         g.FStar_Extraction_ML_UEnv.currentModule expect
                        in
                     FStar_Util.print3
                       "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n"
                       uu____1934 uu____1935 uu____1936)
                 in
              let uu____1937 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect)
                  (FStar_Extraction_ML_Syntax.MLE_Coerce (e, ty1, expect))
                 in
              maybe_eta_expand expect uu____1937
  
let (bv_as_mlty :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun bv  ->
      let uu____1948 = FStar_Extraction_ML_UEnv.lookup_bv g bv  in
      match uu____1948 with
      | FStar_Util.Inl (uu____1949,t) -> t
      | uu____1963 -> FStar_Extraction_ML_Syntax.MLTY_Top
  
let (must_erase :
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g  ->
    fun t  ->
      let rec aux_whnf env t1 =
        let uu____1992 =
          let uu____1993 = FStar_Syntax_Subst.compress t1  in
          uu____1993.FStar_Syntax_Syntax.n  in
        match uu____1992 with
        | FStar_Syntax_Syntax.Tm_type uu____1996 -> true
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid
        | FStar_Syntax_Syntax.Tm_arrow uu____1998 ->
            let uu____2011 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____2011 with
             | (bs,c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs  in
                 let uu____2037 = FStar_Syntax_Util.is_pure_comp c  in
                 if uu____2037
                 then aux env1 (FStar_Syntax_Util.comp_result c)
                 else FStar_Syntax_Util.is_pure_or_ghost_comp c)
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____2039;
               FStar_Syntax_Syntax.index = uu____2040;
               FStar_Syntax_Syntax.sort = t2;_},uu____2042)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____2050,uu____2051) ->
            aux env t2
        | uu____2092 -> false
      
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
        let uu____2099 =
          FStar_Extraction_ML_UEnv.debug g
            (fun uu____2102  ->
               let uu____2103 = FStar_Syntax_Print.term_to_string t2  in
               FStar_Util.print2 "must_erase=%s: %s\n"
                 (if res then "true" else "false") uu____2103)
           in
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
      let arg_as_mlty g1 uu____2147 =
        match uu____2147 with
        | (a,uu____2153) ->
            let uu____2154 = is_type g1 a  in
            if uu____2154
            then translate_term_to_mlty g1 a
            else FStar_Extraction_ML_UEnv.erasedContent
         in
      let fv_app_as_mlty g1 fv args =
        let uu____2169 =
          let uu____2182 =
            FStar_TypeChecker_Env.lookup_lid
              g1.FStar_Extraction_ML_UEnv.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____2182 with
          | ((uu____2203,fvty),uu____2205) ->
              let fvty1 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Normalize.UnfoldUntil
                     FStar_Syntax_Syntax.Delta_constant]
                  g1.FStar_Extraction_ML_UEnv.tcenv fvty
                 in
              FStar_Syntax_Util.arrow_formals fvty1
           in
        match uu____2169 with
        | (formals,uu____2212) ->
            let mlargs = FStar_List.map (arg_as_mlty g1) args  in
            let mlargs1 =
              let n_args = FStar_List.length args  in
              if (FStar_List.length formals) > n_args
              then
                let uu____2256 = FStar_Util.first_N n_args formals  in
                match uu____2256 with
                | (uu____2283,rest) ->
                    let uu____2309 =
                      FStar_List.map
                        (fun uu____2317  ->
                           FStar_Extraction_ML_UEnv.erasedContent) rest
                       in
                    FStar_List.append mlargs uu____2309
              else mlargs  in
            let nm =
              let uu____2324 =
                FStar_Extraction_ML_UEnv.maybe_mangle_type_projector g1 fv
                 in
              match uu____2324 with
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
        | FStar_Syntax_Syntax.Tm_type uu____2340 ->
            FStar_Extraction_ML_Syntax.MLTY_Erased
        | FStar_Syntax_Syntax.Tm_bvar uu____2341 ->
            let uu____2342 =
              let uu____2343 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____2343
               in
            failwith uu____2342
        | FStar_Syntax_Syntax.Tm_delayed uu____2344 ->
            let uu____2369 =
              let uu____2370 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____2370
               in
            failwith uu____2369
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____2371 =
              let uu____2372 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____2372
               in
            failwith uu____2371
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____2374 = FStar_Syntax_Util.unfold_lazy i  in
            translate_term_to_mlty env uu____2374
        | FStar_Syntax_Syntax.Tm_constant uu____2375 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_quoted uu____2376 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_uvar uu____2383 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_meta (t2,uu____2401) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____2406;
               FStar_Syntax_Syntax.index = uu____2407;
               FStar_Syntax_Syntax.sort = t2;_},uu____2409)
            -> translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_uinst (t2,uu____2417) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____2423,uu____2424) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
        | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv []
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let uu____2491 = FStar_Syntax_Subst.open_comp bs c  in
            (match uu____2491 with
             | (bs1,c1) ->
                 let uu____2498 = binders_as_ml_binders env bs1  in
                 (match uu____2498 with
                  | (mlbs,env1) ->
                      let t_ret =
                        let eff =
                          FStar_TypeChecker_Env.norm_eff_name
                            env1.FStar_Extraction_ML_UEnv.tcenv
                            (FStar_Syntax_Util.comp_effect_name c1)
                           in
                        let uu____2525 =
                          let uu____2532 =
                            FStar_TypeChecker_Env.effect_decl_opt
                              env1.FStar_Extraction_ML_UEnv.tcenv eff
                             in
                          FStar_Util.must uu____2532  in
                        match uu____2525 with
                        | (ed,qualifiers) ->
                            let uu____2553 =
                              FStar_All.pipe_right qualifiers
                                (FStar_List.contains
                                   FStar_Syntax_Syntax.Reifiable)
                               in
                            if uu____2553
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
                      let uu____2560 =
                        FStar_List.fold_right
                          (fun uu____2579  ->
                             fun uu____2580  ->
                               match (uu____2579, uu____2580) with
                               | ((uu____2601,t2),(tag,t')) ->
                                   (FStar_Extraction_ML_Syntax.E_PURE,
                                     (FStar_Extraction_ML_Syntax.MLTY_Fun
                                        (t2, tag, t')))) mlbs (erase, t_ret)
                         in
                      (match uu____2560 with | (uu____2613,t2) -> t2)))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let res =
              let uu____2638 =
                let uu____2639 = FStar_Syntax_Util.un_uinst head1  in
                uu____2639.FStar_Syntax_Syntax.n  in
              match uu____2638 with
              | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv args
              | FStar_Syntax_Syntax.Tm_app (head2,args') ->
                  let uu____2666 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_app
                         (head2, (FStar_List.append args' args)))
                      FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                     in
                  translate_term_to_mlty env uu____2666
              | uu____2683 -> FStar_Extraction_ML_UEnv.unknownType  in
            res
        | FStar_Syntax_Syntax.Tm_abs (bs,ty,uu____2686) ->
            let uu____2707 = FStar_Syntax_Subst.open_term bs ty  in
            (match uu____2707 with
             | (bs1,ty1) ->
                 let uu____2714 = binders_as_ml_binders env bs1  in
                 (match uu____2714 with
                  | (bts,env1) -> translate_term_to_mlty env1 ty1))
        | FStar_Syntax_Syntax.Tm_let uu____2739 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_match uu____2752 ->
            FStar_Extraction_ML_UEnv.unknownType
         in
      let rec is_top_ty t =
        match t with
        | FStar_Extraction_ML_Syntax.MLTY_Top  -> true
        | FStar_Extraction_ML_Syntax.MLTY_Named uu____2780 ->
            let uu____2787 = FStar_Extraction_ML_Util.udelta_unfold g t  in
            (match uu____2787 with
             | FStar_Pervasives_Native.None  -> false
             | FStar_Pervasives_Native.Some t1 -> is_top_ty t1)
        | uu____2791 -> false  in
      let uu____2792 = must_erase g t0  in
      if uu____2792
      then FStar_Extraction_ML_Syntax.MLTY_Erased
      else
        (let mlt = aux g t0  in
         let uu____2795 = is_top_ty mlt  in
         if uu____2795
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
      let uu____2810 =
        FStar_All.pipe_right bs
          (FStar_List.fold_left
             (fun uu____2853  ->
                fun b  ->
                  match uu____2853 with
                  | (ml_bs,env) ->
                      let uu____2893 = is_type_binder g b  in
                      if uu____2893
                      then
                        let b1 = FStar_Pervasives_Native.fst b  in
                        let env1 =
                          FStar_Extraction_ML_UEnv.extend_ty env b1
                            (FStar_Pervasives_Native.Some
                               FStar_Extraction_ML_Syntax.MLTY_Top)
                           in
                        let ml_b =
                          let uu____2911 =
                            FStar_Extraction_ML_UEnv.bv_as_ml_termvar b1  in
                          (uu____2911, FStar_Extraction_ML_Syntax.ml_unit_ty)
                           in
                        ((ml_b :: ml_bs), env1)
                      else
                        (let b1 = FStar_Pervasives_Native.fst b  in
                         let t =
                           translate_term_to_mlty env
                             b1.FStar_Syntax_Syntax.sort
                            in
                         let uu____2925 =
                           FStar_Extraction_ML_UEnv.extend_bv env b1 
                             ([], t) false false false
                            in
                         match uu____2925 with
                         | (env1,b2) ->
                             let ml_b =
                               let uu____2949 =
                                 FStar_Extraction_ML_UEnv.removeTick b2  in
                               (uu____2949, t)  in
                             ((ml_b :: ml_bs), env1))) ([], g))
         in
      match uu____2810 with | (ml_bs,env) -> ((FStar_List.rev ml_bs), env)

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
      | (FStar_Extraction_ML_Syntax.MLE_Seq es1,uu____3032) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (FStar_List.append es1 [e2])
      | (uu____3035,FStar_Extraction_ML_Syntax.MLE_Seq es2) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (e1 :: es2)
      | uu____3039 -> FStar_Extraction_ML_Syntax.MLE_Seq [e1; e2]
  
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
                    | uu____3073 when
                        (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
                          =
                          FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr
                        -> body.FStar_Extraction_ML_Syntax.expr
                    | uu____3074 ->
                        mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def
                          body)
             | uu____3075 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body))
        | uu____3078 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body)
  
let (resugar_pat :
  FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option ->
    FStar_Extraction_ML_Syntax.mlpattern ->
      FStar_Extraction_ML_Syntax.mlpattern)
  =
  fun q  ->
    fun p  ->
      match p with
      | FStar_Extraction_ML_Syntax.MLP_CTor (d,pats) ->
          let uu____3099 = FStar_Extraction_ML_Util.is_xtuple d  in
          (match uu____3099 with
           | FStar_Pervasives_Native.Some n1 ->
               FStar_Extraction_ML_Syntax.MLP_Tuple pats
           | uu____3103 ->
               (match q with
                | FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Record_ctor (ty,fns)) ->
                    let path =
                      FStar_List.map FStar_Ident.text_of_id ty.FStar_Ident.ns
                       in
                    let fs = record_fields fns pats  in
                    FStar_Extraction_ML_Syntax.MLP_Record (path, fs)
                | uu____3130 -> p))
      | uu____3133 -> p
  
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
                  let uu____3220 =
                    if Prims.op_Negation ok
                    then
                      FStar_Extraction_ML_UEnv.debug g
                        (fun uu____3224  ->
                           let uu____3225 =
                             FStar_Extraction_ML_Code.string_of_mlty
                               g.FStar_Extraction_ML_UEnv.currentModule t'
                              in
                           let uu____3226 =
                             FStar_Extraction_ML_Code.string_of_mlty
                               g.FStar_Extraction_ML_UEnv.currentModule t
                              in
                           FStar_Util.print2
                             "Expected pattern type %s; got pattern type %s\n"
                             uu____3225 uu____3226)
                    else ()  in
                  ok
               in
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int
                (c,swopt)) when
                let uu____3256 = FStar_Options.codegen ()  in
                uu____3256 <>
                  (FStar_Pervasives_Native.Some FStar_Options.Kremlin)
                ->
                let uu____3261 =
                  match swopt with
                  | FStar_Pervasives_Native.None  ->
                      let uu____3274 =
                        let uu____3275 =
                          let uu____3276 =
                            FStar_Extraction_ML_Util.mlconst_of_const
                              p.FStar_Syntax_Syntax.p
                              (FStar_Const.Const_int
                                 (c, FStar_Pervasives_Native.None))
                             in
                          FStar_Extraction_ML_Syntax.MLE_Const uu____3276  in
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.ml_int_ty) uu____3275
                         in
                      (uu____3274, FStar_Extraction_ML_Syntax.ml_int_ty)
                  | FStar_Pervasives_Native.Some sw ->
                      let source_term =
                        FStar_ToSyntax_ToSyntax.desugar_machine_integer
                          (g.FStar_Extraction_ML_UEnv.tcenv).FStar_TypeChecker_Env.dsenv
                          c sw FStar_Range.dummyRange
                         in
                      let uu____3297 = term_as_mlexpr g source_term  in
                      (match uu____3297 with
                       | (mlterm,uu____3309,mlty) -> (mlterm, mlty))
                   in
                (match uu____3261 with
                 | (mlc,ml_ty) ->
                     let x = FStar_Extraction_ML_Syntax.gensym ()  in
                     let when_clause =
                       let uu____3329 =
                         let uu____3330 =
                           let uu____3337 =
                             let uu____3340 =
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty ml_ty)
                                 (FStar_Extraction_ML_Syntax.MLE_Var x)
                                in
                             [uu____3340; mlc]  in
                           (FStar_Extraction_ML_Util.prims_op_equality,
                             uu____3337)
                            in
                         FStar_Extraction_ML_Syntax.MLE_App uu____3330  in
                       FStar_All.pipe_left
                         (FStar_Extraction_ML_Syntax.with_ty
                            FStar_Extraction_ML_Syntax.ml_bool_ty) uu____3329
                        in
                     let uu____3343 = ok ml_ty  in
                     (g,
                       (FStar_Pervasives_Native.Some
                          ((FStar_Extraction_ML_Syntax.MLP_Var x),
                            [when_clause])), uu____3343))
            | FStar_Syntax_Syntax.Pat_constant s ->
                let t =
                  FStar_TypeChecker_TcTerm.tc_constant
                    g.FStar_Extraction_ML_UEnv.tcenv FStar_Range.dummyRange s
                   in
                let mlty = term_as_mlty g t  in
                let uu____3363 =
                  let uu____3372 =
                    let uu____3379 =
                      let uu____3380 =
                        FStar_Extraction_ML_Util.mlconst_of_const
                          p.FStar_Syntax_Syntax.p s
                         in
                      FStar_Extraction_ML_Syntax.MLP_Const uu____3380  in
                    (uu____3379, [])  in
                  FStar_Pervasives_Native.Some uu____3372  in
                let uu____3389 = ok mlty  in (g, uu____3363, uu____3389)
            | FStar_Syntax_Syntax.Pat_var x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort  in
                let uu____3400 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp
                   in
                (match uu____3400 with
                 | (g1,x1) ->
                     let uu____3423 = ok mlty  in
                     (g1,
                       (if imp
                        then FStar_Pervasives_Native.None
                        else
                          FStar_Pervasives_Native.Some
                            ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                       uu____3423))
            | FStar_Syntax_Syntax.Pat_wild x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort  in
                let uu____3457 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp
                   in
                (match uu____3457 with
                 | (g1,x1) ->
                     let uu____3480 = ok mlty  in
                     (g1,
                       (if imp
                        then FStar_Pervasives_Native.None
                        else
                          FStar_Pervasives_Native.Some
                            ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                       uu____3480))
            | FStar_Syntax_Syntax.Pat_dot_term uu____3512 ->
                (g, FStar_Pervasives_Native.None, true)
            | FStar_Syntax_Syntax.Pat_cons (f,pats) ->
                let uu____3551 =
                  let uu____3556 = FStar_Extraction_ML_UEnv.lookup_fv g f  in
                  match uu____3556 with
                  | FStar_Util.Inr
                      (uu____3561,{
                                    FStar_Extraction_ML_Syntax.expr =
                                      FStar_Extraction_ML_Syntax.MLE_Name n1;
                                    FStar_Extraction_ML_Syntax.mlty =
                                      uu____3563;
                                    FStar_Extraction_ML_Syntax.loc =
                                      uu____3564;_},ttys,uu____3566)
                      -> (n1, ttys)
                  | uu____3579 -> failwith "Expected a constructor"  in
                (match uu____3551 with
                 | (d,tys) ->
                     let nTyVars =
                       FStar_List.length (FStar_Pervasives_Native.fst tys)
                        in
                     let uu____3601 = FStar_Util.first_N nTyVars pats  in
                     (match uu____3601 with
                      | (tysVarPats,restPats) ->
                          let f_ty_opt =
                            try
                              let mlty_args =
                                FStar_All.pipe_right tysVarPats
                                  (FStar_List.map
                                     (fun uu____3734  ->
                                        match uu____3734 with
                                        | (p1,uu____3742) ->
                                            (match p1.FStar_Syntax_Syntax.v
                                             with
                                             | FStar_Syntax_Syntax.Pat_dot_term
                                                 (uu____3747,t) ->
                                                 term_as_mlty g t
                                             | uu____3753 ->
                                                 let uu____3754 =
                                                   FStar_Extraction_ML_UEnv.debug
                                                     g
                                                     (fun uu____3757  ->
                                                        let uu____3758 =
                                                          FStar_Syntax_Print.pat_to_string
                                                            p1
                                                           in
                                                        FStar_Util.print1
                                                          "Pattern %s is not extractable"
                                                          uu____3758)
                                                    in
                                                 FStar_Exn.raise
                                                   Un_extractable)))
                                 in
                              let f_ty =
                                FStar_Extraction_ML_Util.subst tys mlty_args
                                 in
                              let uu____3760 =
                                FStar_Extraction_ML_Util.uncurry_mlty_fun
                                  f_ty
                                 in
                              FStar_Pervasives_Native.Some uu____3760
                            with
                            | Un_extractable  -> FStar_Pervasives_Native.None
                             in
                          let uu____3789 =
                            FStar_Util.fold_map
                              (fun g1  ->
                                 fun uu____3825  ->
                                   match uu____3825 with
                                   | (p1,imp1) ->
                                       let uu____3844 =
                                         extract_one_pat true g1 p1
                                           FStar_Pervasives_Native.None
                                           term_as_mlexpr
                                          in
                                       (match uu____3844 with
                                        | (g2,p2,uu____3873) -> (g2, p2))) g
                              tysVarPats
                             in
                          (match uu____3789 with
                           | (g1,tyMLPats) ->
                               let uu____3934 =
                                 FStar_Util.fold_map
                                   (fun uu____3998  ->
                                      fun uu____3999  ->
                                        match (uu____3998, uu____3999) with
                                        | ((g2,f_ty_opt1),(p1,imp1)) ->
                                            let uu____4092 =
                                              match f_ty_opt1 with
                                              | FStar_Pervasives_Native.Some
                                                  (hd1::rest,res) ->
                                                  ((FStar_Pervasives_Native.Some
                                                      (rest, res)),
                                                    (FStar_Pervasives_Native.Some
                                                       hd1))
                                              | uu____4152 ->
                                                  (FStar_Pervasives_Native.None,
                                                    FStar_Pervasives_Native.None)
                                               in
                                            (match uu____4092 with
                                             | (f_ty_opt2,expected_ty) ->
                                                 let uu____4223 =
                                                   extract_one_pat false g2
                                                     p1 expected_ty
                                                     term_as_mlexpr
                                                    in
                                                 (match uu____4223 with
                                                  | (g3,p2,uu____4264) ->
                                                      ((g3, f_ty_opt2), p2))))
                                   (g1, f_ty_opt) restPats
                                  in
                               (match uu____3934 with
                                | ((g2,f_ty_opt1),restMLPats) ->
                                    let uu____4382 =
                                      let uu____4393 =
                                        FStar_All.pipe_right
                                          (FStar_List.append tyMLPats
                                             restMLPats)
                                          (FStar_List.collect
                                             (fun uu___60_4444  ->
                                                match uu___60_4444 with
                                                | FStar_Pervasives_Native.Some
                                                    x -> [x]
                                                | uu____4486 -> []))
                                         in
                                      FStar_All.pipe_right uu____4393
                                        FStar_List.split
                                       in
                                    (match uu____4382 with
                                     | (mlPats,when_clauses) ->
                                         let pat_ty_compat =
                                           match f_ty_opt1 with
                                           | FStar_Pervasives_Native.Some
                                               ([],t) -> ok t
                                           | uu____4559 -> false  in
                                         let uu____4568 =
                                           let uu____4577 =
                                             let uu____4584 =
                                               resugar_pat
                                                 f.FStar_Syntax_Syntax.fv_qual
                                                 (FStar_Extraction_ML_Syntax.MLP_CTor
                                                    (d, mlPats))
                                                in
                                             let uu____4587 =
                                               FStar_All.pipe_right
                                                 when_clauses
                                                 FStar_List.flatten
                                                in
                                             (uu____4584, uu____4587)  in
                                           FStar_Pervasives_Native.Some
                                             uu____4577
                                            in
                                         (g2, uu____4568, pat_ty_compat))))))
  
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
            let uu____4711 =
              extract_one_pat false g1 p1 expected_t1 term_as_mlexpr  in
            match uu____4711 with
            | (g2,FStar_Pervasives_Native.Some (x,v1),b) -> (g2, (x, v1), b)
            | uu____4768 ->
                failwith "Impossible: Unable to translate pattern"
             in
          let mk_when_clause whens =
            match whens with
            | [] -> FStar_Pervasives_Native.None
            | hd1::tl1 ->
                let uu____4812 =
                  FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd1
                    tl1
                   in
                FStar_Pervasives_Native.Some uu____4812
             in
          let uu____4813 =
            extract_one_pat1 g p (FStar_Pervasives_Native.Some expected_t)
             in
          match uu____4813 with
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
            | FStar_Extraction_ML_Syntax.MLTY_Fun (t0,uu____4961,t1) ->
                let x = FStar_Extraction_ML_Syntax.gensym ()  in
                let uu____4964 =
                  let uu____4975 =
                    let uu____4984 =
                      FStar_All.pipe_left
                        (FStar_Extraction_ML_Syntax.with_ty t0)
                        (FStar_Extraction_ML_Syntax.MLE_Var x)
                       in
                    ((x, t0), uu____4984)  in
                  uu____4975 :: more_args  in
                eta_args uu____4964 t1
            | FStar_Extraction_ML_Syntax.MLTY_Named (uu____4997,uu____4998)
                -> ((FStar_List.rev more_args), t)
            | uu____5021 -> failwith "Impossible: Head type is not an arrow"
             in
          let as_record qual1 e =
            match ((e.FStar_Extraction_ML_Syntax.expr), qual1) with
            | (FStar_Extraction_ML_Syntax.MLE_CTor
               (uu____5051,args),FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Record_ctor (tyname,fields))) ->
                let path =
                  FStar_List.map FStar_Ident.text_of_id tyname.FStar_Ident.ns
                   in
                let fields1 = record_fields fields args  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     e.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_Record (path, fields1))
            | uu____5083 -> e  in
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
                | uu____5255 ->
                    let uu____5258 =
                      let uu____5265 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj
                         in
                      (uu____5265, args)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____5258
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
                     FStar_Extraction_ML_Syntax.mlty = uu____5269;
                     FStar_Extraction_ML_Syntax.loc = uu____5270;_},uu____5271);
                FStar_Extraction_ML_Syntax.mlty = uu____5272;
                FStar_Extraction_ML_Syntax.loc = uu____5273;_},mle::args),FStar_Pervasives_Native.Some
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
                | uu____5304 ->
                    let uu____5307 =
                      let uu____5314 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj
                         in
                      (uu____5314, args)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____5307
                 in
              FStar_Extraction_ML_Syntax.with_ty
                mlAppExpr.FStar_Extraction_ML_Syntax.mlty e
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____5318;
                FStar_Extraction_ML_Syntax.loc = uu____5319;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____5327 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5327
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____5331;
                FStar_Extraction_ML_Syntax.loc = uu____5332;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____5334)) ->
              let uu____5347 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5347
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____5351;
                     FStar_Extraction_ML_Syntax.loc = uu____5352;_},uu____5353);
                FStar_Extraction_ML_Syntax.mlty = uu____5354;
                FStar_Extraction_ML_Syntax.loc = uu____5355;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____5367 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5367
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____5371;
                     FStar_Extraction_ML_Syntax.loc = uu____5372;_},uu____5373);
                FStar_Extraction_ML_Syntax.mlty = uu____5374;
                FStar_Extraction_ML_Syntax.loc = uu____5375;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____5377)) ->
              let uu____5394 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5394
          | (FStar_Extraction_ML_Syntax.MLE_Name
             mlp,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor
             )) ->
              let uu____5400 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5400
          | (FStar_Extraction_ML_Syntax.MLE_Name
             mlp,FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____5404)) ->
              let uu____5413 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5413
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____5417;
                FStar_Extraction_ML_Syntax.loc = uu____5418;_},uu____5419),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____5426 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5426
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____5430;
                FStar_Extraction_ML_Syntax.loc = uu____5431;_},uu____5432),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____5433)) ->
              let uu____5446 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5446
          | uu____5449 -> mlAppExpr
  
let (maybe_downgrade_eff :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.e_tag ->
      FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.e_tag)
  =
  fun g  ->
    fun f  ->
      fun t  ->
        let rec non_informative1 t1 =
          let uu____5476 =
            (type_leq g t1 FStar_Extraction_ML_Syntax.ml_unit_ty) ||
              (erasableType g t1)
             in
          if uu____5476
          then true
          else
            (match t1 with
             | FStar_Extraction_ML_Syntax.MLTY_Fun
                 (uu____5478,FStar_Extraction_ML_Syntax.E_PURE ,t2) ->
                 non_informative1 t2
             | FStar_Extraction_ML_Syntax.MLTY_Fun
                 (uu____5480,FStar_Extraction_ML_Syntax.E_GHOST ,t2) ->
                 non_informative1 t2
             | uu____5482 -> false)
           in
        let uu____5483 =
          (f = FStar_Extraction_ML_Syntax.E_GHOST) && (non_informative1 t)
           in
        if uu____5483 then FStar_Extraction_ML_Syntax.E_PURE else f
  
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
          let uu____5549 =
            FStar_Extraction_ML_UEnv.debug g
              (fun uu____5553  ->
                 let uu____5554 = FStar_Syntax_Print.term_to_string e  in
                 let uu____5555 =
                   FStar_Extraction_ML_Code.string_of_mlty
                     g.FStar_Extraction_ML_UEnv.currentModule ty
                    in
                 FStar_Util.print2 "Checking %s at type %s\n" uu____5554
                   uu____5555)
             in
          match (f, ty) with
          | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____5560) ->
              (FStar_Extraction_ML_Syntax.ml_unit,
                FStar_Extraction_ML_Syntax.MLTY_Erased)
          | (FStar_Extraction_ML_Syntax.E_PURE
             ,FStar_Extraction_ML_Syntax.MLTY_Erased ) ->
              (FStar_Extraction_ML_Syntax.ml_unit,
                FStar_Extraction_ML_Syntax.MLTY_Erased)
          | uu____5561 ->
              let uu____5566 = term_as_mlexpr g e  in
              (match uu____5566 with
               | (ml_e,tag,t) ->
                   let uu____5580 = FStar_Extraction_ML_Util.eff_leq tag f
                      in
                   if uu____5580
                   then
                     let uu____5585 = maybe_coerce g ml_e t ty  in
                     (uu____5585, ty)
                   else
                     (match (tag, f, ty) with
                      | (FStar_Extraction_ML_Syntax.E_GHOST
                         ,FStar_Extraction_ML_Syntax.E_PURE
                         ,FStar_Extraction_ML_Syntax.MLTY_Erased ) ->
                          let uu____5591 = maybe_coerce g ml_e t ty  in
                          (uu____5591, ty)
                      | uu____5592 ->
                          let uu____5599 = err_unexpected_eff g e ty f tag
                             in
                          let uu____5600 = maybe_coerce g ml_e t ty  in
                          (uu____5600, ty)))

and (term_as_mlexpr' :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Extraction_ML_Syntax.mlexpr,FStar_Extraction_ML_Syntax.e_tag,
        FStar_Extraction_ML_Syntax.mlty) FStar_Pervasives_Native.tuple3)
  =
  fun g  ->
    fun top  ->
      let uu____5609 =
        FStar_Extraction_ML_UEnv.debug g
          (fun u  ->
             let uu____5613 =
               let uu____5614 =
                 FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos  in
               let uu____5615 = FStar_Syntax_Print.tag_of_term top  in
               let uu____5616 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.format3 "%s: term_as_mlexpr' (%s) :  %s \n"
                 uu____5614 uu____5615 uu____5616
                in
             FStar_Util.print_string uu____5613)
         in
      let t = FStar_Syntax_Subst.compress top  in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____5624 =
            let uu____5625 = FStar_Syntax_Print.tag_of_term t  in
            FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5625
             in
          failwith uu____5624
      | FStar_Syntax_Syntax.Tm_delayed uu____5632 ->
          let uu____5657 =
            let uu____5658 = FStar_Syntax_Print.tag_of_term t  in
            FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5658
             in
          failwith uu____5657
      | FStar_Syntax_Syntax.Tm_uvar uu____5665 ->
          let uu____5682 =
            let uu____5683 = FStar_Syntax_Print.tag_of_term t  in
            FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5683
             in
          failwith uu____5682
      | FStar_Syntax_Syntax.Tm_bvar uu____5690 ->
          let uu____5691 =
            let uu____5692 = FStar_Syntax_Print.tag_of_term t  in
            FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5692
             in
          failwith uu____5691
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____5700 = FStar_Syntax_Util.unfold_lazy i  in
          term_as_mlexpr' g uu____5700
      | FStar_Syntax_Syntax.Tm_type uu____5701 ->
          (FStar_Extraction_ML_Syntax.ml_unit,
            FStar_Extraction_ML_Syntax.E_PURE,
            FStar_Extraction_ML_Syntax.ml_unit_ty)
      | FStar_Syntax_Syntax.Tm_refine uu____5702 ->
          (FStar_Extraction_ML_Syntax.ml_unit,
            FStar_Extraction_ML_Syntax.E_PURE,
            FStar_Extraction_ML_Syntax.ml_unit_ty)
      | FStar_Syntax_Syntax.Tm_arrow uu____5709 ->
          (FStar_Extraction_ML_Syntax.ml_unit,
            FStar_Extraction_ML_Syntax.E_PURE,
            FStar_Extraction_ML_Syntax.ml_unit_ty)
      | FStar_Syntax_Syntax.Tm_quoted
          (qt,{
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic ;
                FStar_Syntax_Syntax.antiquotes = uu____5723;_})
          ->
          let uu____5738 =
            let uu____5747 =
              let uu____5764 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.failwith_lid
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Extraction_ML_UEnv.lookup_fv g uu____5764  in
            FStar_All.pipe_left FStar_Util.right uu____5747  in
          (match uu____5738 with
           | (uu____5807,fw,uu____5809,uu____5810) ->
               let uu____5811 =
                 let uu____5812 =
                   let uu____5813 =
                     let uu____5820 =
                       let uu____5823 =
                         FStar_All.pipe_left
                           (FStar_Extraction_ML_Syntax.with_ty
                              FStar_Extraction_ML_Syntax.ml_string_ty)
                           (FStar_Extraction_ML_Syntax.MLE_Const
                              (FStar_Extraction_ML_Syntax.MLC_String
                                 "Open quotation at runtime"))
                          in
                       [uu____5823]  in
                     (fw, uu____5820)  in
                   FStar_Extraction_ML_Syntax.MLE_App uu____5813  in
                 FStar_All.pipe_left
                   (FStar_Extraction_ML_Syntax.with_ty
                      FStar_Extraction_ML_Syntax.ml_int_ty) uu____5812
                  in
               (uu____5811, FStar_Extraction_ML_Syntax.E_PURE,
                 FStar_Extraction_ML_Syntax.ml_int_ty))
      | FStar_Syntax_Syntax.Tm_quoted
          (qt,{
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static ;
                FStar_Syntax_Syntax.antiquotes = aqs;_})
          ->
          let uu____5842 = FStar_Reflection_Basic.inspect_ln qt  in
          (match uu____5842 with
           | FStar_Reflection_Data.Tv_Var bv ->
               let uu____5850 = FStar_Syntax_Syntax.lookup_aq bv aqs  in
               (match uu____5850 with
                | FStar_Pervasives_Native.Some (false ,tm) ->
                    term_as_mlexpr' g tm
                | FStar_Pervasives_Native.Some (true ,tm) ->
                    let uu____5873 =
                      let uu____5882 =
                        let uu____5899 =
                          FStar_Syntax_Syntax.lid_as_fv
                            FStar_Parser_Const.failwith_lid
                            FStar_Syntax_Syntax.Delta_constant
                            FStar_Pervasives_Native.None
                           in
                        FStar_Extraction_ML_UEnv.lookup_fv g uu____5899  in
                      FStar_All.pipe_left FStar_Util.right uu____5882  in
                    (match uu____5873 with
                     | (uu____5942,fw,uu____5944,uu____5945) ->
                         let uu____5946 =
                           let uu____5947 =
                             let uu____5948 =
                               let uu____5955 =
                                 let uu____5958 =
                                   FStar_All.pipe_left
                                     (FStar_Extraction_ML_Syntax.with_ty
                                        FStar_Extraction_ML_Syntax.ml_string_ty)
                                     (FStar_Extraction_ML_Syntax.MLE_Const
                                        (FStar_Extraction_ML_Syntax.MLC_String
                                           "Open quotation at runtime"))
                                    in
                                 [uu____5958]  in
                               (fw, uu____5955)  in
                             FStar_Extraction_ML_Syntax.MLE_App uu____5948
                              in
                           FStar_All.pipe_left
                             (FStar_Extraction_ML_Syntax.with_ty
                                FStar_Extraction_ML_Syntax.ml_int_ty)
                             uu____5947
                            in
                         (uu____5946, FStar_Extraction_ML_Syntax.E_PURE,
                           FStar_Extraction_ML_Syntax.ml_int_ty))
                | FStar_Pervasives_Native.None  ->
                    let tv =
                      let uu____5966 =
                        FStar_Reflection_Embeddings.e_term_view_aq aqs  in
                      FStar_Syntax_Embeddings.embed uu____5966
                        t.FStar_Syntax_Syntax.pos
                        (FStar_Reflection_Data.Tv_Var bv)
                       in
                    let t1 =
                      let uu____5972 =
                        let uu____5981 = FStar_Syntax_Syntax.as_arg tv  in
                        [uu____5981]  in
                      FStar_Syntax_Util.mk_app
                        (FStar_Reflection_Data.refl_constant_term
                           FStar_Reflection_Data.fstar_refl_pack_ln)
                        uu____5972
                       in
                    term_as_mlexpr' g t1)
           | tv ->
               let tv1 =
                 let uu____5984 =
                   FStar_Reflection_Embeddings.e_term_view_aq aqs  in
                 FStar_Syntax_Embeddings.embed uu____5984
                   t.FStar_Syntax_Syntax.pos tv
                  in
               let t1 =
                 let uu____5990 =
                   let uu____5999 = FStar_Syntax_Syntax.as_arg tv1  in
                   [uu____5999]  in
                 FStar_Syntax_Util.mk_app
                   (FStar_Reflection_Data.refl_constant_term
                      FStar_Reflection_Data.fstar_refl_pack_ln) uu____5990
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
          (t1,FStar_Syntax_Syntax.Meta_monadic (m,uu____6013)) ->
          let t2 = FStar_Syntax_Subst.compress t1  in
          (match t2.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) when
               FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname ->
               let uu____6043 =
                 let uu____6050 =
                   FStar_TypeChecker_Env.effect_decl_opt
                     g.FStar_Extraction_ML_UEnv.tcenv m
                    in
                 FStar_Util.must uu____6050  in
               (match uu____6043 with
                | (ed,qualifiers) ->
                    let uu____6077 =
                      let uu____6078 =
                        FStar_All.pipe_right qualifiers
                          (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                         in
                      FStar_All.pipe_right uu____6078 Prims.op_Negation  in
                    if uu____6077
                    then term_as_mlexpr' g t2
                    else
                      failwith
                        "This should not happen (should have been handled at Tm_abs level)")
           | uu____6094 -> term_as_mlexpr' g t2)
      | FStar_Syntax_Syntax.Tm_meta (t1,uu____6096) -> term_as_mlexpr' g t1
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____6102) -> term_as_mlexpr' g t1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____6108 =
            FStar_TypeChecker_TcTerm.type_of_tot_term
              g.FStar_Extraction_ML_UEnv.tcenv t
             in
          (match uu____6108 with
           | (uu____6121,ty,uu____6123) ->
               let ml_ty = term_as_mlty g ty  in
               let uu____6125 =
                 let uu____6126 =
                   FStar_Extraction_ML_Util.mlexpr_of_const
                     t.FStar_Syntax_Syntax.pos c
                    in
                 FStar_Extraction_ML_Syntax.with_ty ml_ty uu____6126  in
               (uu____6125, FStar_Extraction_ML_Syntax.E_PURE, ml_ty))
      | FStar_Syntax_Syntax.Tm_name uu____6127 ->
          let uu____6128 = is_type g t  in
          if uu____6128
          then
            (FStar_Extraction_ML_Syntax.ml_unit,
              FStar_Extraction_ML_Syntax.E_PURE,
              FStar_Extraction_ML_Syntax.ml_unit_ty)
          else
            (let uu____6136 = FStar_Extraction_ML_UEnv.lookup_term g t  in
             match uu____6136 with
             | (FStar_Util.Inl uu____6149,uu____6150) ->
                 (FStar_Extraction_ML_Syntax.ml_unit,
                   FStar_Extraction_ML_Syntax.E_PURE,
                   FStar_Extraction_ML_Syntax.ml_unit_ty)
             | (FStar_Util.Inr (uu____6187,x,mltys,uu____6190),qual) ->
                 (match mltys with
                  | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                      ->
                      (FStar_Extraction_ML_Syntax.ml_unit,
                        FStar_Extraction_ML_Syntax.E_PURE, t1)
                  | ([],t1) ->
                      let uu____6236 =
                        maybe_eta_data_and_project_record g qual t1 x  in
                      (uu____6236, FStar_Extraction_ML_Syntax.E_PURE, t1)
                  | uu____6237 -> err_uninst g t mltys t))
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____6245 = is_type g t  in
          if uu____6245
          then
            (FStar_Extraction_ML_Syntax.ml_unit,
              FStar_Extraction_ML_Syntax.E_PURE,
              FStar_Extraction_ML_Syntax.ml_unit_ty)
          else
            (let uu____6253 = FStar_Extraction_ML_UEnv.try_lookup_fv g fv  in
             match uu____6253 with
             | FStar_Pervasives_Native.None  ->
                 (FStar_Extraction_ML_Syntax.ml_unit,
                   FStar_Extraction_ML_Syntax.E_PURE,
                   FStar_Extraction_ML_Syntax.MLTY_Erased)
             | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____6262) ->
                 (FStar_Extraction_ML_Syntax.ml_unit,
                   FStar_Extraction_ML_Syntax.E_PURE,
                   FStar_Extraction_ML_Syntax.ml_unit_ty)
             | FStar_Pervasives_Native.Some (FStar_Util.Inr
                 (uu____6295,x,mltys,uu____6298)) ->
                 (match mltys with
                  | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                      ->
                      (FStar_Extraction_ML_Syntax.ml_unit,
                        FStar_Extraction_ML_Syntax.E_PURE, t1)
                  | ([],t1) ->
                      let uu____6339 =
                        maybe_eta_data_and_project_record g
                          fv.FStar_Syntax_Syntax.fv_qual t1 x
                         in
                      (uu____6339, FStar_Extraction_ML_Syntax.E_PURE, t1)
                  | uu____6340 -> err_uninst g t mltys t))
      | FStar_Syntax_Syntax.Tm_abs (bs,body,copt) ->
          let uu____6370 = FStar_Syntax_Subst.open_term bs body  in
          (match uu____6370 with
           | (bs1,body1) ->
               let uu____6383 = binders_as_ml_binders g bs1  in
               (match uu____6383 with
                | (ml_bs,env) ->
                    let body2 =
                      match copt with
                      | FStar_Pervasives_Native.Some c ->
                          let uu____6416 =
                            FStar_TypeChecker_Env.is_reifiable
                              env.FStar_Extraction_ML_UEnv.tcenv c
                             in
                          if uu____6416
                          then
                            FStar_TypeChecker_Util.reify_body
                              env.FStar_Extraction_ML_UEnv.tcenv body1
                          else body1
                      | FStar_Pervasives_Native.None  ->
                          let uu____6418 =
                            FStar_Extraction_ML_UEnv.debug g
                              (fun uu____6421  ->
                                 let uu____6422 =
                                   FStar_Syntax_Print.term_to_string body1
                                    in
                                 FStar_Util.print1
                                   "No computation type for: %s\n" uu____6422)
                             in
                          body1
                       in
                    let uu____6423 = term_as_mlexpr env body2  in
                    (match uu____6423 with
                     | (ml_body,f,t1) ->
                         let uu____6439 =
                           FStar_List.fold_right
                             (fun uu____6458  ->
                                fun uu____6459  ->
                                  match (uu____6458, uu____6459) with
                                  | ((uu____6480,targ),(f1,t2)) ->
                                      (FStar_Extraction_ML_Syntax.E_PURE,
                                        (FStar_Extraction_ML_Syntax.MLTY_Fun
                                           (targ, f1, t2)))) ml_bs (f, t1)
                            in
                         (match uu____6439 with
                          | (f1,tfun) ->
                              let uu____6500 =
                                FStar_All.pipe_left
                                  (FStar_Extraction_ML_Syntax.with_ty tfun)
                                  (FStar_Extraction_ML_Syntax.MLE_Fun
                                     (ml_bs, ml_body))
                                 in
                              (uu____6500, f1, tfun)))))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____6507;
             FStar_Syntax_Syntax.vars = uu____6508;_},(a1,uu____6510)::[])
          ->
          let ty =
            let uu____6540 =
              FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid  in
            term_as_mlty g uu____6540  in
          let uu____6541 =
            let uu____6542 =
              FStar_Extraction_ML_Util.mlexpr_of_range
                a1.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty)
              uu____6542
             in
          (uu____6541, FStar_Extraction_ML_Syntax.E_PURE, ty)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____6543;
             FStar_Syntax_Syntax.vars = uu____6544;_},(t1,uu____6546)::
           (r,uu____6548)::[])
          -> term_as_mlexpr' g t1
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_reflect uu____6587);
             FStar_Syntax_Syntax.pos = uu____6588;
             FStar_Syntax_Syntax.vars = uu____6589;_},uu____6590)
          -> failwith "Unreachable? Tm_app Const_reflect"
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let is_total rc =
            (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
               FStar_Parser_Const.effect_Tot_lid)
              ||
              (FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
                 (FStar_List.existsb
                    (fun uu___61_6647  ->
                       match uu___61_6647 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | uu____6648 -> false)))
             in
          let uu____6649 =
            let uu____6654 =
              let uu____6655 = FStar_Syntax_Subst.compress head1  in
              uu____6655.FStar_Syntax_Syntax.n  in
            ((head1.FStar_Syntax_Syntax.n), uu____6654)  in
          (match uu____6649 with
           | (FStar_Syntax_Syntax.Tm_uvar uu____6664,uu____6665) ->
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
           | (uu____6683,FStar_Syntax_Syntax.Tm_abs
              (bs,uu____6685,FStar_Pervasives_Native.Some rc)) when
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
           | (uu____6706,FStar_Syntax_Syntax.Tm_constant
              (FStar_Const.Const_reify )) ->
               let e =
                 let uu____6708 = FStar_List.hd args  in
                 FStar_TypeChecker_Util.reify_body_with_arg
                   g.FStar_Extraction_ML_UEnv.tcenv head1 uu____6708
                  in
               let tm =
                 let uu____6718 =
                   let uu____6721 = FStar_TypeChecker_Util.remove_reify e  in
                   let uu____6722 = FStar_List.tl args  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____6721 uu____6722  in
                 uu____6718 FStar_Pervasives_Native.None
                   t.FStar_Syntax_Syntax.pos
                  in
               term_as_mlexpr' g tm
           | uu____6731 ->
               let rec extract_app is_data uu____6780 uu____6781 restArgs =
                 match (uu____6780, uu____6781) with
                 | ((mlhead,mlargs_f),(f,t1)) ->
                     (match (restArgs, t1) with
                      | ([],uu____6871) ->
                          let mlargs =
                            FStar_All.pipe_right (FStar_List.rev mlargs_f)
                              (FStar_List.map FStar_Pervasives_Native.fst)
                             in
                          let app =
                            let uu____6906 =
                              FStar_All.pipe_left
                                (FStar_Extraction_ML_Syntax.with_ty t1)
                                (FStar_Extraction_ML_Syntax.MLE_App
                                   (mlhead, mlargs))
                               in
                            FStar_All.pipe_left
                              (maybe_eta_data_and_project_record g is_data t1)
                              uu____6906
                             in
                          (app, f, t1)
                      | ((arg,uu____6910)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                         (formal_t,f',t2)) when
                          (is_type g arg) &&
                            (type_leq g formal_t
                               FStar_Extraction_ML_Syntax.ml_unit_ty)
                          ->
                          let uu____6941 =
                            let uu____6946 =
                              FStar_Extraction_ML_Util.join
                                arg.FStar_Syntax_Syntax.pos f f'
                               in
                            (uu____6946, t2)  in
                          extract_app is_data
                            (mlhead,
                              ((FStar_Extraction_ML_Syntax.ml_unit,
                                 FStar_Extraction_ML_Syntax.E_PURE) ::
                              mlargs_f)) uu____6941 rest
                      | ((e0,uu____6958)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                         (tExpected,f',t2)) ->
                          let r = e0.FStar_Syntax_Syntax.pos  in
                          let expected_effect =
                            let uu____6991 =
                              (FStar_Options.lax ()) &&
                                (FStar_TypeChecker_Util.short_circuit_head
                                   head1)
                               in
                            if uu____6991
                            then FStar_Extraction_ML_Syntax.E_IMPURE
                            else FStar_Extraction_ML_Syntax.E_PURE  in
                          let uu____6993 =
                            check_term_as_mlexpr g e0 expected_effect
                              tExpected
                             in
                          (match uu____6993 with
                           | (e01,tInferred) ->
                               let uu____7006 =
                                 let uu____7011 =
                                   FStar_Extraction_ML_Util.join_l r [f; f']
                                    in
                                 (uu____7011, t2)  in
                               extract_app is_data
                                 (mlhead, ((e01, expected_effect) ::
                                   mlargs_f)) uu____7006 rest)
                      | uu____7022 ->
                          let uu____7035 =
                            FStar_Extraction_ML_Util.udelta_unfold g t1  in
                          (match uu____7035 with
                           | FStar_Pervasives_Native.Some t2 ->
                               extract_app is_data (mlhead, mlargs_f) 
                                 (f, t2) restArgs
                           | FStar_Pervasives_Native.None  ->
                               (match t1 with
                                | FStar_Extraction_ML_Syntax.MLTY_Erased  ->
                                    (FStar_Extraction_ML_Syntax.ml_unit,
                                      FStar_Extraction_ML_Syntax.E_PURE, t1)
                                | uu____7057 ->
                                    err_ill_typed_application g top restArgs
                                      t1)))
                  in
               let extract_app_maybe_projector is_data mlhead uu____7103
                 args1 =
                 match uu____7103 with
                 | (f,t1) ->
                     (match is_data with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Record_projector uu____7135)
                          ->
                          let rec remove_implicits args2 f1 t2 =
                            match (args2, t2) with
                            | ((a0,FStar_Pervasives_Native.Some
                                (FStar_Syntax_Syntax.Implicit uu____7216))::args3,FStar_Extraction_ML_Syntax.MLTY_Fun
                               (uu____7218,f',t3)) ->
                                let uu____7255 =
                                  FStar_Extraction_ML_Util.join
                                    a0.FStar_Syntax_Syntax.pos f1 f'
                                   in
                                remove_implicits args3 uu____7255 t3
                            | uu____7256 -> (args2, f1, t2)  in
                          let uu____7281 = remove_implicits args1 f t1  in
                          (match uu____7281 with
                           | (args2,f1,t2) ->
                               extract_app is_data (mlhead, []) (f1, t2)
                                 args2)
                      | uu____7337 ->
                          extract_app is_data (mlhead, []) (f, t1) args1)
                  in
               let extract_app_with_instantiations uu____7360 =
                 let head2 = FStar_Syntax_Util.un_uinst head1  in
                 match head2.FStar_Syntax_Syntax.n with
                 | FStar_Syntax_Syntax.Tm_name uu____7368 ->
                     let uu____7369 =
                       let uu____7382 =
                         FStar_Extraction_ML_UEnv.lookup_term g head2  in
                       match uu____7382 with
                       | (FStar_Util.Inr (uu____7401,x1,x2,x3),q) ->
                           ((x1, x2, x3), q)
                       | uu____7446 -> failwith "FIXME Ty"  in
                     (match uu____7369 with
                      | ((head_ml,(vars,t1),inst_ok),qual) ->
                          let has_typ_apps =
                            match args with
                            | (a,uu____7496)::uu____7497 -> is_type g a
                            | uu____7516 -> false  in
                          let uu____7525 =
                            match vars with
                            | uu____7554::uu____7555 when
                                (Prims.op_Negation has_typ_apps) && inst_ok
                                -> (head_ml, t1, args)
                            | uu____7566 ->
                                let n1 = FStar_List.length vars  in
                                if n1 <= (FStar_List.length args)
                                then
                                  let uu____7594 = FStar_Util.first_N n1 args
                                     in
                                  (match uu____7594 with
                                   | (prefix1,rest) ->
                                       let prefixAsMLTypes =
                                         FStar_List.map
                                           (fun uu____7683  ->
                                              match uu____7683 with
                                              | (x,uu____7689) ->
                                                  term_as_mlty g x) prefix1
                                          in
                                       let t2 =
                                         instantiate (vars, t1)
                                           prefixAsMLTypes
                                          in
                                       let mk_tapp e ty_args =
                                         match ty_args with
                                         | [] -> e
                                         | uu____7704 ->
                                             let uu___65_7707 = e  in
                                             {
                                               FStar_Extraction_ML_Syntax.expr
                                                 =
                                                 (FStar_Extraction_ML_Syntax.MLE_TApp
                                                    (e, ty_args));
                                               FStar_Extraction_ML_Syntax.mlty
                                                 =
                                                 (uu___65_7707.FStar_Extraction_ML_Syntax.mlty);
                                               FStar_Extraction_ML_Syntax.loc
                                                 =
                                                 (uu___65_7707.FStar_Extraction_ML_Syntax.loc)
                                             }
                                          in
                                       let head3 =
                                         match head_ml.FStar_Extraction_ML_Syntax.expr
                                         with
                                         | FStar_Extraction_ML_Syntax.MLE_Name
                                             uu____7711 ->
                                             let uu___66_7712 =
                                               mk_tapp head_ml
                                                 prefixAsMLTypes
                                                in
                                             {
                                               FStar_Extraction_ML_Syntax.expr
                                                 =
                                                 (uu___66_7712.FStar_Extraction_ML_Syntax.expr);
                                               FStar_Extraction_ML_Syntax.mlty
                                                 = t2;
                                               FStar_Extraction_ML_Syntax.loc
                                                 =
                                                 (uu___66_7712.FStar_Extraction_ML_Syntax.loc)
                                             }
                                         | FStar_Extraction_ML_Syntax.MLE_Var
                                             uu____7713 ->
                                             let uu___66_7714 =
                                               mk_tapp head_ml
                                                 prefixAsMLTypes
                                                in
                                             {
                                               FStar_Extraction_ML_Syntax.expr
                                                 =
                                                 (uu___66_7714.FStar_Extraction_ML_Syntax.expr);
                                               FStar_Extraction_ML_Syntax.mlty
                                                 = t2;
                                               FStar_Extraction_ML_Syntax.loc
                                                 =
                                                 (uu___66_7714.FStar_Extraction_ML_Syntax.loc)
                                             }
                                         | FStar_Extraction_ML_Syntax.MLE_App
                                             (head3,{
                                                      FStar_Extraction_ML_Syntax.expr
                                                        =
                                                        FStar_Extraction_ML_Syntax.MLE_Const
                                                        (FStar_Extraction_ML_Syntax.MLC_Unit
                                                        );
                                                      FStar_Extraction_ML_Syntax.mlty
                                                        = uu____7716;
                                                      FStar_Extraction_ML_Syntax.loc
                                                        = uu____7717;_}::[])
                                             ->
                                             FStar_All.pipe_right
                                               (FStar_Extraction_ML_Syntax.MLE_App
                                                  ((let uu___67_7723 =
                                                      mk_tapp head3
                                                        prefixAsMLTypes
                                                       in
                                                    {
                                                      FStar_Extraction_ML_Syntax.expr
                                                        =
                                                        (uu___67_7723.FStar_Extraction_ML_Syntax.expr);
                                                      FStar_Extraction_ML_Syntax.mlty
                                                        =
                                                        (FStar_Extraction_ML_Syntax.MLTY_Fun
                                                           (FStar_Extraction_ML_Syntax.ml_unit_ty,
                                                             FStar_Extraction_ML_Syntax.E_PURE,
                                                             t2));
                                                      FStar_Extraction_ML_Syntax.loc
                                                        =
                                                        (uu___67_7723.FStar_Extraction_ML_Syntax.loc)
                                                    }),
                                                    [FStar_Extraction_ML_Syntax.ml_unit]))
                                               (FStar_Extraction_ML_Syntax.with_ty
                                                  t2)
                                         | uu____7724 ->
                                             failwith
                                               "Impossible: Unexpected head term"
                                          in
                                       (head3, t2, rest))
                                else err_uninst g head2 (vars, t1) top
                             in
                          (match uu____7525 with
                           | (head_ml1,head_t,args1) ->
                               (match args1 with
                                | [] ->
                                    let uu____7785 =
                                      maybe_eta_data_and_project_record g
                                        qual head_t head_ml1
                                       in
                                    (uu____7785,
                                      FStar_Extraction_ML_Syntax.E_PURE,
                                      head_t)
                                | uu____7786 ->
                                    extract_app_maybe_projector qual head_ml1
                                      (FStar_Extraction_ML_Syntax.E_PURE,
                                        head_t) args1)))
                 | FStar_Syntax_Syntax.Tm_fvar uu____7795 ->
                     let uu____7796 =
                       let uu____7809 =
                         FStar_Extraction_ML_UEnv.lookup_term g head2  in
                       match uu____7809 with
                       | (FStar_Util.Inr (uu____7828,x1,x2,x3),q) ->
                           ((x1, x2, x3), q)
                       | uu____7873 -> failwith "FIXME Ty"  in
                     (match uu____7796 with
                      | ((head_ml,(vars,t1),inst_ok),qual) ->
                          let has_typ_apps =
                            match args with
                            | (a,uu____7923)::uu____7924 -> is_type g a
                            | uu____7943 -> false  in
                          let uu____7952 =
                            match vars with
                            | uu____7981::uu____7982 when
                                (Prims.op_Negation has_typ_apps) && inst_ok
                                -> (head_ml, t1, args)
                            | uu____7993 ->
                                let n1 = FStar_List.length vars  in
                                if n1 <= (FStar_List.length args)
                                then
                                  let uu____8021 = FStar_Util.first_N n1 args
                                     in
                                  (match uu____8021 with
                                   | (prefix1,rest) ->
                                       let prefixAsMLTypes =
                                         FStar_List.map
                                           (fun uu____8110  ->
                                              match uu____8110 with
                                              | (x,uu____8116) ->
                                                  term_as_mlty g x) prefix1
                                          in
                                       let t2 =
                                         instantiate (vars, t1)
                                           prefixAsMLTypes
                                          in
                                       let mk_tapp e ty_args =
                                         match ty_args with
                                         | [] -> e
                                         | uu____8131 ->
                                             let uu___65_8134 = e  in
                                             {
                                               FStar_Extraction_ML_Syntax.expr
                                                 =
                                                 (FStar_Extraction_ML_Syntax.MLE_TApp
                                                    (e, ty_args));
                                               FStar_Extraction_ML_Syntax.mlty
                                                 =
                                                 (uu___65_8134.FStar_Extraction_ML_Syntax.mlty);
                                               FStar_Extraction_ML_Syntax.loc
                                                 =
                                                 (uu___65_8134.FStar_Extraction_ML_Syntax.loc)
                                             }
                                          in
                                       let head3 =
                                         match head_ml.FStar_Extraction_ML_Syntax.expr
                                         with
                                         | FStar_Extraction_ML_Syntax.MLE_Name
                                             uu____8138 ->
                                             let uu___66_8139 =
                                               mk_tapp head_ml
                                                 prefixAsMLTypes
                                                in
                                             {
                                               FStar_Extraction_ML_Syntax.expr
                                                 =
                                                 (uu___66_8139.FStar_Extraction_ML_Syntax.expr);
                                               FStar_Extraction_ML_Syntax.mlty
                                                 = t2;
                                               FStar_Extraction_ML_Syntax.loc
                                                 =
                                                 (uu___66_8139.FStar_Extraction_ML_Syntax.loc)
                                             }
                                         | FStar_Extraction_ML_Syntax.MLE_Var
                                             uu____8140 ->
                                             let uu___66_8141 =
                                               mk_tapp head_ml
                                                 prefixAsMLTypes
                                                in
                                             {
                                               FStar_Extraction_ML_Syntax.expr
                                                 =
                                                 (uu___66_8141.FStar_Extraction_ML_Syntax.expr);
                                               FStar_Extraction_ML_Syntax.mlty
                                                 = t2;
                                               FStar_Extraction_ML_Syntax.loc
                                                 =
                                                 (uu___66_8141.FStar_Extraction_ML_Syntax.loc)
                                             }
                                         | FStar_Extraction_ML_Syntax.MLE_App
                                             (head3,{
                                                      FStar_Extraction_ML_Syntax.expr
                                                        =
                                                        FStar_Extraction_ML_Syntax.MLE_Const
                                                        (FStar_Extraction_ML_Syntax.MLC_Unit
                                                        );
                                                      FStar_Extraction_ML_Syntax.mlty
                                                        = uu____8143;
                                                      FStar_Extraction_ML_Syntax.loc
                                                        = uu____8144;_}::[])
                                             ->
                                             FStar_All.pipe_right
                                               (FStar_Extraction_ML_Syntax.MLE_App
                                                  ((let uu___67_8150 =
                                                      mk_tapp head3
                                                        prefixAsMLTypes
                                                       in
                                                    {
                                                      FStar_Extraction_ML_Syntax.expr
                                                        =
                                                        (uu___67_8150.FStar_Extraction_ML_Syntax.expr);
                                                      FStar_Extraction_ML_Syntax.mlty
                                                        =
                                                        (FStar_Extraction_ML_Syntax.MLTY_Fun
                                                           (FStar_Extraction_ML_Syntax.ml_unit_ty,
                                                             FStar_Extraction_ML_Syntax.E_PURE,
                                                             t2));
                                                      FStar_Extraction_ML_Syntax.loc
                                                        =
                                                        (uu___67_8150.FStar_Extraction_ML_Syntax.loc)
                                                    }),
                                                    [FStar_Extraction_ML_Syntax.ml_unit]))
                                               (FStar_Extraction_ML_Syntax.with_ty
                                                  t2)
                                         | uu____8151 ->
                                             failwith
                                               "Impossible: Unexpected head term"
                                          in
                                       (head3, t2, rest))
                                else err_uninst g head2 (vars, t1) top
                             in
                          (match uu____7952 with
                           | (head_ml1,head_t,args1) ->
                               (match args1 with
                                | [] ->
                                    let uu____8212 =
                                      maybe_eta_data_and_project_record g
                                        qual head_t head_ml1
                                       in
                                    (uu____8212,
                                      FStar_Extraction_ML_Syntax.E_PURE,
                                      head_t)
                                | uu____8213 ->
                                    extract_app_maybe_projector qual head_ml1
                                      (FStar_Extraction_ML_Syntax.E_PURE,
                                        head_t) args1)))
                 | uu____8222 ->
                     let uu____8223 = term_as_mlexpr g head2  in
                     (match uu____8223 with
                      | (head3,f,t1) ->
                          extract_app_maybe_projector
                            FStar_Pervasives_Native.None head3 (f, t1) args)
                  in
               let uu____8239 = is_type g t  in
               if uu____8239
               then
                 (FStar_Extraction_ML_Syntax.ml_unit,
                   FStar_Extraction_ML_Syntax.E_PURE,
                   FStar_Extraction_ML_Syntax.ml_unit_ty)
               else
                 (let uu____8247 =
                    let uu____8248 = FStar_Syntax_Util.un_uinst head1  in
                    uu____8248.FStar_Syntax_Syntax.n  in
                  match uu____8247 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____8258 =
                        FStar_Extraction_ML_UEnv.try_lookup_fv g fv  in
                      (match uu____8258 with
                       | FStar_Pervasives_Native.None  ->
                           (FStar_Extraction_ML_Syntax.ml_unit,
                             FStar_Extraction_ML_Syntax.E_PURE,
                             FStar_Extraction_ML_Syntax.MLTY_Erased)
                       | uu____8267 -> extract_app_with_instantiations ())
                  | uu____8270 -> extract_app_with_instantiations ()))
      | FStar_Syntax_Syntax.Tm_ascribed (e0,(tc,uu____8273),f) ->
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
          let uu____8340 = check_term_as_mlexpr g e0 f1 t1  in
          (match uu____8340 with | (e,t2) -> (e, f1, t2))
      | FStar_Syntax_Syntax.Tm_let ((is_rec,lbs),e') ->
          let top_level = FStar_Syntax_Syntax.is_top_level lbs  in
          let uu____8371 =
            if is_rec
            then FStar_Syntax_Subst.open_let_rec lbs e'
            else
              (let uu____8385 = FStar_Syntax_Syntax.is_top_level lbs  in
               if uu____8385
               then (lbs, e')
               else
                 (let lb = FStar_List.hd lbs  in
                  let x =
                    let uu____8399 =
                      FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                    FStar_Syntax_Syntax.freshen_bv uu____8399  in
                  let lb1 =
                    let uu___68_8401 = lb  in
                    {
                      FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___68_8401.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp =
                        (uu___68_8401.FStar_Syntax_Syntax.lbtyp);
                      FStar_Syntax_Syntax.lbeff =
                        (uu___68_8401.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef =
                        (uu___68_8401.FStar_Syntax_Syntax.lbdef);
                      FStar_Syntax_Syntax.lbattrs =
                        (uu___68_8401.FStar_Syntax_Syntax.lbattrs);
                      FStar_Syntax_Syntax.lbpos =
                        (uu___68_8401.FStar_Syntax_Syntax.lbpos)
                    }  in
                  let e'1 =
                    FStar_Syntax_Subst.subst
                      [FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x)] e'
                     in
                  ([lb1], e'1)))
             in
          (match uu____8371 with
           | (lbs1,e'1) ->
               let lbs2 =
                 if top_level
                 then
                   FStar_All.pipe_right lbs1
                     (FStar_List.map
                        (fun lb  ->
                           let tcenv =
                             let uu____8432 =
                               FStar_Ident.lid_of_path
                                 (FStar_List.append
                                    (FStar_Pervasives_Native.fst
                                       g.FStar_Extraction_ML_UEnv.currentModule)
                                    [FStar_Pervasives_Native.snd
                                       g.FStar_Extraction_ML_UEnv.currentModule])
                                 FStar_Range.dummyRange
                                in
                             FStar_TypeChecker_Env.set_current_module
                               g.FStar_Extraction_ML_UEnv.tcenv uu____8432
                              in
                           let lbdef =
                             let uu____8440 = FStar_Options.ml_ish ()  in
                             if uu____8440
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
                           let uu___69_8444 = lb  in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___69_8444.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___69_8444.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___69_8444.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___69_8444.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = lbdef;
                             FStar_Syntax_Syntax.lbattrs =
                               (uu___69_8444.FStar_Syntax_Syntax.lbattrs);
                             FStar_Syntax_Syntax.lbpos =
                               (uu___69_8444.FStar_Syntax_Syntax.lbpos)
                           }))
                 else lbs1  in
               let maybe_generalize uu____8468 =
                 match uu____8468 with
                 | { FStar_Syntax_Syntax.lbname = lbname_;
                     FStar_Syntax_Syntax.lbunivs = uu____8488;
                     FStar_Syntax_Syntax.lbtyp = t1;
                     FStar_Syntax_Syntax.lbeff = lbeff;
                     FStar_Syntax_Syntax.lbdef = e;
                     FStar_Syntax_Syntax.lbattrs = uu____8492;
                     FStar_Syntax_Syntax.lbpos = uu____8493;_} ->
                     let f_e = effect_as_etag g lbeff  in
                     let t2 = FStar_Syntax_Subst.compress t1  in
                     let no_gen uu____8568 =
                       let expected_t = term_as_mlty g t2  in
                       (lbname_, f_e, (t2, ([], ([], expected_t))), false, e)
                        in
                     if Prims.op_Negation top_level
                     then no_gen ()
                     else
                       (let uu____8649 = must_erase g t2  in
                        if uu____8649
                        then
                          (lbname_, f_e,
                            (t2,
                              ([],
                                ([], FStar_Extraction_ML_Syntax.MLTY_Erased))),
                            false, e)
                        else
                          (match t2.FStar_Syntax_Syntax.n with
                           | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                               let uu____8765 = FStar_List.hd bs  in
                               FStar_All.pipe_right uu____8765
                                 (is_type_binder g)
                               ->
                               let uu____8778 =
                                 FStar_Syntax_Subst.open_comp bs c  in
                               (match uu____8778 with
                                | (bs1,c1) ->
                                    let uu____8803 =
                                      let uu____8810 =
                                        FStar_Util.prefix_until
                                          (fun x  ->
                                             let uu____8846 =
                                               is_type_binder g x  in
                                             Prims.op_Negation uu____8846)
                                          bs1
                                         in
                                      match uu____8810 with
                                      | FStar_Pervasives_Native.None  ->
                                          (bs1,
                                            (FStar_Syntax_Util.comp_result c1))
                                      | FStar_Pervasives_Native.Some
                                          (bs2,b,rest) ->
                                          let uu____8934 =
                                            FStar_Syntax_Util.arrow (b ::
                                              rest) c1
                                             in
                                          (bs2, uu____8934)
                                       in
                                    (match uu____8803 with
                                     | (tbinders,tbody) ->
                                         let n_tbinders =
                                           FStar_List.length tbinders  in
                                         let e1 =
                                           let uu____8979 = normalize_abs e
                                              in
                                           FStar_All.pipe_right uu____8979
                                             FStar_Syntax_Util.unmeta
                                            in
                                         (match e1.FStar_Syntax_Syntax.n with
                                          | FStar_Syntax_Syntax.Tm_abs
                                              (bs2,body,copt) ->
                                              let uu____9021 =
                                                FStar_Syntax_Subst.open_term
                                                  bs2 body
                                                 in
                                              (match uu____9021 with
                                               | (bs3,body1) ->
                                                   if
                                                     n_tbinders <=
                                                       (FStar_List.length bs3)
                                                   then
                                                     let uu____9074 =
                                                       FStar_Util.first_N
                                                         n_tbinders bs3
                                                        in
                                                     (match uu____9074 with
                                                      | (targs,rest_args) ->
                                                          let expected_source_ty
                                                            =
                                                            let s =
                                                              FStar_List.map2
                                                                (fun
                                                                   uu____9162
                                                                    ->
                                                                   fun
                                                                    uu____9163
                                                                     ->
                                                                    match 
                                                                    (uu____9162,
                                                                    uu____9163)
                                                                    with
                                                                    | 
                                                                    ((x,uu____9181),
                                                                    (y,uu____9183))
                                                                    ->
                                                                    let uu____9192
                                                                    =
                                                                    let uu____9199
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    y  in
                                                                    (x,
                                                                    uu____9199)
                                                                     in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____9192)
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
                                                                   uu____9210
                                                                    ->
                                                                   match uu____9210
                                                                   with
                                                                   | 
                                                                   (a,uu____9216)
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
                                                            let uu____9225 =
                                                              FStar_All.pipe_right
                                                                targs
                                                                (FStar_List.map
                                                                   (fun
                                                                    uu____9243
                                                                     ->
                                                                    match uu____9243
                                                                    with
                                                                    | 
                                                                    (x,uu____9249)
                                                                    ->
                                                                    FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                                    x))
                                                               in
                                                            (uu____9225,
                                                              expected_t)
                                                             in
                                                          let add_unit =
                                                            match rest_args
                                                            with
                                                            | [] ->
                                                                let uu____9257
                                                                  =
                                                                  is_fstar_value
                                                                    body1
                                                                   in
                                                                Prims.op_Negation
                                                                  uu____9257
                                                            | uu____9258 ->
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
                                                            else polytype  in
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
                                              uu____9327 ->
                                              let env =
                                                FStar_List.fold_left
                                                  (fun env  ->
                                                     fun uu____9344  ->
                                                       match uu____9344 with
                                                       | (a,uu____9350) ->
                                                           FStar_Extraction_ML_UEnv.extend_ty
                                                             env a
                                                             FStar_Pervasives_Native.None)
                                                  g tbinders
                                                 in
                                              let expected_t =
                                                term_as_mlty env tbody  in
                                              let polytype =
                                                let uu____9359 =
                                                  FStar_All.pipe_right
                                                    tbinders
                                                    (FStar_List.map
                                                       (fun uu____9371  ->
                                                          match uu____9371
                                                          with
                                                          | (x,uu____9377) ->
                                                              FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                                x))
                                                   in
                                                (uu____9359, expected_t)  in
                                              let args =
                                                FStar_All.pipe_right tbinders
                                                  (FStar_List.map
                                                     (fun uu____9393  ->
                                                        match uu____9393 with
                                                        | (bv,uu____9399) ->
                                                            let uu____9400 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                bv
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____9400
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
                                              uu____9442 ->
                                              let env =
                                                FStar_List.fold_left
                                                  (fun env  ->
                                                     fun uu____9453  ->
                                                       match uu____9453 with
                                                       | (a,uu____9459) ->
                                                           FStar_Extraction_ML_UEnv.extend_ty
                                                             env a
                                                             FStar_Pervasives_Native.None)
                                                  g tbinders
                                                 in
                                              let expected_t =
                                                term_as_mlty env tbody  in
                                              let polytype =
                                                let uu____9468 =
                                                  FStar_All.pipe_right
                                                    tbinders
                                                    (FStar_List.map
                                                       (fun uu____9480  ->
                                                          match uu____9480
                                                          with
                                                          | (x,uu____9486) ->
                                                              FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                                x))
                                                   in
                                                (uu____9468, expected_t)  in
                                              let args =
                                                FStar_All.pipe_right tbinders
                                                  (FStar_List.map
                                                     (fun uu____9502  ->
                                                        match uu____9502 with
                                                        | (bv,uu____9508) ->
                                                            let uu____9509 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                bv
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____9509
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
                                              uu____9551 ->
                                              let env =
                                                FStar_List.fold_left
                                                  (fun env  ->
                                                     fun uu____9562  ->
                                                       match uu____9562 with
                                                       | (a,uu____9568) ->
                                                           FStar_Extraction_ML_UEnv.extend_ty
                                                             env a
                                                             FStar_Pervasives_Native.None)
                                                  g tbinders
                                                 in
                                              let expected_t =
                                                term_as_mlty env tbody  in
                                              let polytype =
                                                let uu____9577 =
                                                  FStar_All.pipe_right
                                                    tbinders
                                                    (FStar_List.map
                                                       (fun uu____9589  ->
                                                          match uu____9589
                                                          with
                                                          | (x,uu____9595) ->
                                                              FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                                x))
                                                   in
                                                (uu____9577, expected_t)  in
                                              let args =
                                                FStar_All.pipe_right tbinders
                                                  (FStar_List.map
                                                     (fun uu____9611  ->
                                                        match uu____9611 with
                                                        | (bv,uu____9617) ->
                                                            let uu____9618 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                bv
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____9618
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
                                          | uu____9660 ->
                                              err_value_restriction e1)))
                           | uu____9679 -> no_gen ()))
                  in
               let check_lb env uu____9724 =
                 match uu____9724 with
                 | (nm,(lbname,f,(t1,(targs,polytype)),add_unit,e)) ->
                     let env1 =
                       FStar_List.fold_left
                         (fun env1  ->
                            fun uu____9859  ->
                              match uu____9859 with
                              | (a,uu____9865) ->
                                  FStar_Extraction_ML_UEnv.extend_ty env1 a
                                    FStar_Pervasives_Native.None) env targs
                        in
                     let expected_t = FStar_Pervasives_Native.snd polytype
                        in
                     let uu____9867 =
                       check_term_as_mlexpr env1 e f expected_t  in
                     (match uu____9867 with
                      | (e1,ty) ->
                          let f1 = maybe_downgrade_eff env1 f expected_t  in
                          let meta =
                            match ty with
                            | FStar_Extraction_ML_Syntax.MLTY_Erased  ->
                                [FStar_Extraction_ML_Syntax.Erased]
                            | uu____9884 -> []  in
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
               let uu____9950 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____10041  ->
                        match uu____10041 with
                        | (env,lbs4) ->
                            let uu____10166 = lb  in
                            (match uu____10166 with
                             | (lbname,uu____10214,(t1,(uu____10216,polytype)),add_unit,uu____10219)
                                 ->
                                 let uu____10232 =
                                   FStar_Extraction_ML_UEnv.extend_lb env
                                     lbname t1 polytype add_unit true
                                    in
                                 (match uu____10232 with
                                  | (env1,nm) -> (env1, ((nm, lb) :: lbs4)))))
                   lbs3 (g, [])
                  in
               (match uu____9950 with
                | (env_body,lbs4) ->
                    let env_def = if is_rec then env_body else g  in
                    let lbs5 =
                      FStar_All.pipe_right lbs4
                        (FStar_List.map (check_lb env_def))
                       in
                    let e'_rng = e'1.FStar_Syntax_Syntax.pos  in
                    let uu____10509 = term_as_mlexpr env_body e'1  in
                    (match uu____10509 with
                     | (e'2,f',t') ->
                         let f =
                           let uu____10526 =
                             let uu____10529 =
                               FStar_List.map FStar_Pervasives_Native.fst
                                 lbs5
                                in
                             f' :: uu____10529  in
                           FStar_Extraction_ML_Util.join_l e'_rng uu____10526
                            in
                         let is_rec1 =
                           if is_rec = true
                           then FStar_Extraction_ML_Syntax.Rec
                           else FStar_Extraction_ML_Syntax.NonRec  in
                         let uu____10538 =
                           let uu____10539 =
                             let uu____10540 =
                               let uu____10541 =
                                 FStar_List.map FStar_Pervasives_Native.snd
                                   lbs5
                                  in
                               (is_rec1, uu____10541)  in
                             mk_MLE_Let top_level uu____10540 e'2  in
                           let uu____10550 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               t.FStar_Syntax_Syntax.pos
                              in
                           FStar_Extraction_ML_Syntax.with_ty_loc t'
                             uu____10539 uu____10550
                            in
                         (uu____10538, f, t'))))
      | FStar_Syntax_Syntax.Tm_match (scrutinee,pats) ->
          let uu____10589 = term_as_mlexpr g scrutinee  in
          (match uu____10589 with
           | (e,f_e,t_e) ->
               let uu____10605 = check_pats_for_ite pats  in
               (match uu____10605 with
                | (b,then_e,else_e) ->
                    let no_lift x t1 = x  in
                    if b
                    then
                      (match (then_e, else_e) with
                       | (FStar_Pervasives_Native.Some
                          then_e1,FStar_Pervasives_Native.Some else_e1) ->
                           let uu____10664 = term_as_mlexpr g then_e1  in
                           (match uu____10664 with
                            | (then_mle,f_then,t_then) ->
                                let uu____10680 = term_as_mlexpr g else_e1
                                   in
                                (match uu____10680 with
                                 | (else_mle,f_else,t_else) ->
                                     let uu____10696 =
                                       let uu____10707 =
                                         type_leq g t_then t_else  in
                                       if uu____10707
                                       then (t_else, no_lift)
                                       else
                                         (let uu____10725 =
                                            type_leq g t_else t_then  in
                                          if uu____10725
                                          then (t_then, no_lift)
                                          else
                                            (FStar_Extraction_ML_Syntax.MLTY_Top,
                                              FStar_Extraction_ML_Syntax.apply_obj_repr))
                                        in
                                     (match uu____10696 with
                                      | (t_branch,maybe_lift1) ->
                                          let uu____10769 =
                                            let uu____10770 =
                                              let uu____10771 =
                                                let uu____10780 =
                                                  maybe_lift1 then_mle t_then
                                                   in
                                                let uu____10781 =
                                                  let uu____10784 =
                                                    maybe_lift1 else_mle
                                                      t_else
                                                     in
                                                  FStar_Pervasives_Native.Some
                                                    uu____10784
                                                   in
                                                (e, uu____10780, uu____10781)
                                                 in
                                              FStar_Extraction_ML_Syntax.MLE_If
                                                uu____10771
                                               in
                                            FStar_All.pipe_left
                                              (FStar_Extraction_ML_Syntax.with_ty
                                                 t_branch) uu____10770
                                             in
                                          let uu____10787 =
                                            FStar_Extraction_ML_Util.join
                                              then_e1.FStar_Syntax_Syntax.pos
                                              f_then f_else
                                             in
                                          (uu____10769, uu____10787,
                                            t_branch))))
                       | uu____10788 ->
                           failwith
                             "ITE pats matched but then and else expressions not found?")
                    else
                      (let uu____10804 =
                         FStar_All.pipe_right pats
                           (FStar_Util.fold_map
                              (fun compat  ->
                                 fun br  ->
                                   let uu____10913 =
                                     FStar_Syntax_Subst.open_branch br  in
                                   match uu____10913 with
                                   | (pat,when_opt,branch1) ->
                                       let uu____10957 =
                                         extract_pat g pat t_e term_as_mlexpr
                                          in
                                       (match uu____10957 with
                                        | (env,p,pat_t_compat) ->
                                            let uu____11015 =
                                              match when_opt with
                                              | FStar_Pervasives_Native.None 
                                                  ->
                                                  (FStar_Pervasives_Native.None,
                                                    FStar_Extraction_ML_Syntax.E_PURE)
                                              | FStar_Pervasives_Native.Some
                                                  w ->
                                                  let uu____11037 =
                                                    term_as_mlexpr env w  in
                                                  (match uu____11037 with
                                                   | (w1,f_w,t_w) ->
                                                       let w2 =
                                                         maybe_coerce env w1
                                                           t_w
                                                           FStar_Extraction_ML_Syntax.ml_bool_ty
                                                          in
                                                       ((FStar_Pervasives_Native.Some
                                                           w2), f_w))
                                               in
                                            (match uu____11015 with
                                             | (when_opt1,f_when) ->
                                                 let uu____11086 =
                                                   term_as_mlexpr env branch1
                                                    in
                                                 (match uu____11086 with
                                                  | (mlbranch,f_branch,t_branch)
                                                      ->
                                                      let uu____11120 =
                                                        FStar_All.pipe_right
                                                          p
                                                          (FStar_List.map
                                                             (fun uu____11197
                                                                 ->
                                                                match uu____11197
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
                                                        uu____11120))))) true)
                          in
                       match uu____10804 with
                       | (pat_t_compat,mlbranches) ->
                           let mlbranches1 = FStar_List.flatten mlbranches
                              in
                           let e1 =
                             if pat_t_compat
                             then e
                             else
                               (let uu____11358 =
                                  FStar_Extraction_ML_UEnv.debug g
                                    (fun uu____11362  ->
                                       let uu____11363 =
                                         FStar_Extraction_ML_Code.string_of_mlexpr
                                           g.FStar_Extraction_ML_UEnv.currentModule
                                           e
                                          in
                                       let uu____11364 =
                                         FStar_Extraction_ML_Code.string_of_mlty
                                           g.FStar_Extraction_ML_UEnv.currentModule
                                           t_e
                                          in
                                       FStar_Util.print2
                                         "Coercing scrutinee %s from type %s because pattern type is incompatible\n"
                                         uu____11363 uu____11364)
                                   in
                                FStar_All.pipe_left
                                  (FStar_Extraction_ML_Syntax.with_ty t_e)
                                  (FStar_Extraction_ML_Syntax.MLE_Coerce
                                     (e, t_e,
                                       FStar_Extraction_ML_Syntax.MLTY_Top)))
                              in
                           (match mlbranches1 with
                            | [] ->
                                let uu____11389 =
                                  let uu____11398 =
                                    let uu____11415 =
                                      FStar_Syntax_Syntax.lid_as_fv
                                        FStar_Parser_Const.failwith_lid
                                        FStar_Syntax_Syntax.Delta_constant
                                        FStar_Pervasives_Native.None
                                       in
                                    FStar_Extraction_ML_UEnv.lookup_fv g
                                      uu____11415
                                     in
                                  FStar_All.pipe_left FStar_Util.right
                                    uu____11398
                                   in
                                (match uu____11389 with
                                 | (uu____11458,fw,uu____11460,uu____11461)
                                     ->
                                     let uu____11462 =
                                       let uu____11463 =
                                         let uu____11464 =
                                           let uu____11471 =
                                             let uu____11474 =
                                               FStar_All.pipe_left
                                                 (FStar_Extraction_ML_Syntax.with_ty
                                                    FStar_Extraction_ML_Syntax.ml_string_ty)
                                                 (FStar_Extraction_ML_Syntax.MLE_Const
                                                    (FStar_Extraction_ML_Syntax.MLC_String
                                                       "unreachable"))
                                                in
                                             [uu____11474]  in
                                           (fw, uu____11471)  in
                                         FStar_Extraction_ML_Syntax.MLE_App
                                           uu____11464
                                          in
                                       FStar_All.pipe_left
                                         (FStar_Extraction_ML_Syntax.with_ty
                                            FStar_Extraction_ML_Syntax.ml_int_ty)
                                         uu____11463
                                        in
                                     (uu____11462,
                                       FStar_Extraction_ML_Syntax.E_PURE,
                                       FStar_Extraction_ML_Syntax.ml_int_ty))
                            | (uu____11477,uu____11478,(uu____11479,f_first,t_first))::rest
                                ->
                                let uu____11539 =
                                  FStar_List.fold_left
                                    (fun uu____11581  ->
                                       fun uu____11582  ->
                                         match (uu____11581, uu____11582)
                                         with
                                         | ((topt,f),(uu____11639,uu____11640,
                                                      (uu____11641,f_branch,t_branch)))
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
                                                   let uu____11697 =
                                                     type_leq g t1 t_branch
                                                      in
                                                   if uu____11697
                                                   then
                                                     FStar_Pervasives_Native.Some
                                                       t_branch
                                                   else
                                                     (let uu____11701 =
                                                        type_leq g t_branch
                                                          t1
                                                         in
                                                      if uu____11701
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
                                (match uu____11539 with
                                 | (topt,f_match) ->
                                     let mlbranches2 =
                                       FStar_All.pipe_right mlbranches1
                                         (FStar_List.map
                                            (fun uu____11796  ->
                                               match uu____11796 with
                                               | (p,(wopt,uu____11825),
                                                  (b1,uu____11827,t1)) ->
                                                   let b2 =
                                                     match topt with
                                                     | FStar_Pervasives_Native.None
                                                          ->
                                                         FStar_Extraction_ML_Syntax.apply_obj_repr
                                                           b1 t1
                                                     | FStar_Pervasives_Native.Some
                                                         uu____11846 -> b1
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
                                     let uu____11851 =
                                       FStar_All.pipe_left
                                         (FStar_Extraction_ML_Syntax.with_ty
                                            t_match)
                                         (FStar_Extraction_ML_Syntax.MLE_Match
                                            (e1, mlbranches2))
                                        in
                                     (uu____11851, f_match, t_match))))))

let (ind_discriminator_body :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlmodule1)
  =
  fun env  ->
    fun discName  ->
      fun constrName  ->
        let uu____11877 =
          let uu____11882 =
            FStar_TypeChecker_Env.lookup_lid
              env.FStar_Extraction_ML_UEnv.tcenv discName
             in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____11882  in
        match uu____11877 with
        | (uu____11907,fstar_disc_type) ->
            let wildcards =
              let uu____11916 =
                let uu____11917 = FStar_Syntax_Subst.compress fstar_disc_type
                   in
                uu____11917.FStar_Syntax_Syntax.n  in
              match uu____11916 with
              | FStar_Syntax_Syntax.Tm_arrow (binders,uu____11927) ->
                  let uu____11944 =
                    FStar_All.pipe_right binders
                      (FStar_List.filter
                         (fun uu___62_11976  ->
                            match uu___62_11976 with
                            | (uu____11983,FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____11984)) ->
                                true
                            | uu____11987 -> false))
                     in
                  FStar_All.pipe_right uu____11944
                    (FStar_List.map
                       (fun uu____12020  ->
                          let uu____12027 = fresh "_"  in
                          (uu____12027, FStar_Extraction_ML_Syntax.MLTY_Top)))
              | uu____12028 -> failwith "Discriminator must be a function"
               in
            let mlid = fresh "_discr_"  in
            let targ = FStar_Extraction_ML_Syntax.MLTY_Top  in
            let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top  in
            let discrBody =
              let uu____12039 =
                let uu____12040 =
                  let uu____12051 =
                    let uu____12052 =
                      let uu____12053 =
                        let uu____12068 =
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty targ)
                            (FStar_Extraction_ML_Syntax.MLE_Name ([], mlid))
                           in
                        let uu____12071 =
                          let uu____12082 =
                            let uu____12091 =
                              let uu____12092 =
                                let uu____12099 =
                                  FStar_Extraction_ML_Syntax.mlpath_of_lident
                                    constrName
                                   in
                                (uu____12099,
                                  [FStar_Extraction_ML_Syntax.MLP_Wild])
                                 in
                              FStar_Extraction_ML_Syntax.MLP_CTor uu____12092
                               in
                            let uu____12102 =
                              FStar_All.pipe_left
                                (FStar_Extraction_ML_Syntax.with_ty
                                   FStar_Extraction_ML_Syntax.ml_bool_ty)
                                (FStar_Extraction_ML_Syntax.MLE_Const
                                   (FStar_Extraction_ML_Syntax.MLC_Bool true))
                               in
                            (uu____12091, FStar_Pervasives_Native.None,
                              uu____12102)
                             in
                          let uu____12105 =
                            let uu____12116 =
                              let uu____12125 =
                                FStar_All.pipe_left
                                  (FStar_Extraction_ML_Syntax.with_ty
                                     FStar_Extraction_ML_Syntax.ml_bool_ty)
                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                     (FStar_Extraction_ML_Syntax.MLC_Bool
                                        false))
                                 in
                              (FStar_Extraction_ML_Syntax.MLP_Wild,
                                FStar_Pervasives_Native.None, uu____12125)
                               in
                            [uu____12116]  in
                          uu____12082 :: uu____12105  in
                        (uu____12068, uu____12071)  in
                      FStar_Extraction_ML_Syntax.MLE_Match uu____12053  in
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.ml_bool_ty) uu____12052
                     in
                  ((FStar_List.append wildcards [(mlid, targ)]), uu____12051)
                   in
                FStar_Extraction_ML_Syntax.MLE_Fun uu____12040  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty disc_ty) uu____12039
               in
            let uu____12180 =
              let uu____12181 =
                let uu____12184 =
                  let uu____12185 =
                    FStar_Extraction_ML_UEnv.convIdent
                      discName.FStar_Ident.ident
                     in
                  {
                    FStar_Extraction_ML_Syntax.mllb_name = uu____12185;
                    FStar_Extraction_ML_Syntax.mllb_tysc =
                      FStar_Pervasives_Native.None;
                    FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                    FStar_Extraction_ML_Syntax.mllb_def = discrBody;
                    FStar_Extraction_ML_Syntax.mllb_meta = [];
                    FStar_Extraction_ML_Syntax.print_typ = false
                  }  in
                [uu____12184]  in
              (FStar_Extraction_ML_Syntax.NonRec, uu____12181)  in
            FStar_Extraction_ML_Syntax.MLM_Let uu____12180
  