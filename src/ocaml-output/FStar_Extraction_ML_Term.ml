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
          (match uu____573 with | (head1,uu____587) -> is_arity env head1)
      | FStar_Syntax_Syntax.Tm_uinst (head1,uu____605) -> is_arity env head1
      | FStar_Syntax_Syntax.Tm_refine (x,uu____611) ->
          is_arity env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_abs (uu____616,body,uu____618) ->
          is_arity env body
      | FStar_Syntax_Syntax.Tm_let (uu____639,body) -> is_arity env body
      | FStar_Syntax_Syntax.Tm_match (uu____657,branches) ->
          (match branches with
           | (uu____695,uu____696,e)::uu____698 -> is_arity env e
           | uu____745 -> false)
  
let rec (is_type_aux :
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____773 ->
          let uu____798 =
            let uu____799 = FStar_Syntax_Print.tag_of_term t1  in
            FStar_Util.format1 "Impossible: %s" uu____799  in
          failwith uu____798
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____800 =
            let uu____801 = FStar_Syntax_Print.tag_of_term t1  in
            FStar_Util.format1 "Impossible: %s" uu____801  in
          failwith uu____800
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____803 = FStar_Syntax_Util.unfold_lazy i  in
          is_type_aux env uu____803
      | FStar_Syntax_Syntax.Tm_constant uu____804 -> false
      | FStar_Syntax_Syntax.Tm_type uu____805 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____806 -> true
      | FStar_Syntax_Syntax.Tm_arrow uu____813 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.failwith_lid ->
          false
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Extraction_ML_UEnv.is_type_name env fv
      | FStar_Syntax_Syntax.Tm_uvar
          { FStar_Syntax_Syntax.ctx_uvar_head = uu____828;
            FStar_Syntax_Syntax.ctx_uvar_gamma = uu____829;
            FStar_Syntax_Syntax.ctx_uvar_binders = uu____830;
            FStar_Syntax_Syntax.ctx_uvar_typ = t2;
            FStar_Syntax_Syntax.ctx_uvar_reason = uu____832;
            FStar_Syntax_Syntax.ctx_uvar_should_check = uu____833;
            FStar_Syntax_Syntax.ctx_uvar_range = uu____834;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_bvar
          { FStar_Syntax_Syntax.ppname = uu____855;
            FStar_Syntax_Syntax.index = uu____856;
            FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_name
          { FStar_Syntax_Syntax.ppname = uu____860;
            FStar_Syntax_Syntax.index = uu____861;
            FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____866,uu____867) ->
          is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____909) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____916) ->
          let uu____937 = FStar_Syntax_Subst.open_term bs body  in
          (match uu____937 with | (uu____942,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
          let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
          let uu____959 =
            let uu____964 =
              let uu____965 = FStar_Syntax_Syntax.mk_binder x  in [uu____965]
               in
            FStar_Syntax_Subst.open_term uu____964 body  in
          (match uu____959 with | (uu____978,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_let ((uu____980,lbs),body) ->
          let uu____997 = FStar_Syntax_Subst.open_let_rec lbs body  in
          (match uu____997 with | (uu____1004,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_match (uu____1010,branches) ->
          (match branches with
           | b::uu____1049 ->
               let uu____1094 = FStar_Syntax_Subst.open_branch b  in
               (match uu____1094 with
                | (uu____1095,uu____1096,e) -> is_type_aux env e)
           | uu____1114 -> false)
      | FStar_Syntax_Syntax.Tm_quoted uu____1131 -> false
      | FStar_Syntax_Syntax.Tm_meta (t2,uu____1139) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_app (head1,uu____1145) ->
          is_type_aux env head1
  
let (is_type :
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      FStar_Extraction_ML_UEnv.debug env
        (fun uu____1180  ->
           let uu____1181 = FStar_Syntax_Print.tag_of_term t  in
           let uu____1182 = FStar_Syntax_Print.term_to_string t  in
           FStar_Util.print2 "checking is_type (%s) %s\n" uu____1181
             uu____1182);
      (let b = is_type_aux env t  in
       FStar_Extraction_ML_UEnv.debug env
         (fun uu____1188  ->
            if b
            then
              let uu____1189 = FStar_Syntax_Print.term_to_string t  in
              let uu____1190 = FStar_Syntax_Print.tag_of_term t  in
              FStar_Util.print2 "is_type %s (%s)\n" uu____1189 uu____1190
            else
              (let uu____1192 = FStar_Syntax_Print.term_to_string t  in
               let uu____1193 = FStar_Syntax_Print.tag_of_term t  in
               FStar_Util.print2 "not a type %s (%s)\n" uu____1192 uu____1193));
       b)
  
let is_type_binder :
  'Auu____1200 .
    FStar_Extraction_ML_UEnv.env ->
      (FStar_Syntax_Syntax.bv,'Auu____1200) FStar_Pervasives_Native.tuple2 ->
        Prims.bool
  =
  fun env  ->
    fun x  ->
      is_arity env (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
  
let (is_constructor : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1224 =
      let uu____1225 = FStar_Syntax_Subst.compress t  in
      uu____1225.FStar_Syntax_Syntax.n  in
    match uu____1224 with
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____1228;
          FStar_Syntax_Syntax.fv_delta = uu____1229;
          FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
            (FStar_Syntax_Syntax.Data_ctor );_}
        -> true
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____1230;
          FStar_Syntax_Syntax.fv_delta = uu____1231;
          FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
            (FStar_Syntax_Syntax.Record_ctor uu____1232);_}
        -> true
    | uu____1239 -> false
  
let rec (is_fstar_value : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1245 =
      let uu____1246 = FStar_Syntax_Subst.compress t  in
      uu____1246.FStar_Syntax_Syntax.n  in
    match uu____1245 with
    | FStar_Syntax_Syntax.Tm_constant uu____1249 -> true
    | FStar_Syntax_Syntax.Tm_bvar uu____1250 -> true
    | FStar_Syntax_Syntax.Tm_fvar uu____1251 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____1252 -> true
    | FStar_Syntax_Syntax.Tm_app (head1,args) ->
        let uu____1291 = is_constructor head1  in
        if uu____1291
        then
          FStar_All.pipe_right args
            (FStar_List.for_all
               (fun uu____1305  ->
                  match uu____1305 with
                  | (te,uu____1311) -> is_fstar_value te))
        else false
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____1314) -> is_fstar_value t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____1320,uu____1321) ->
        is_fstar_value t1
    | uu____1362 -> false
  
let rec (is_ml_value : FStar_Extraction_ML_Syntax.mlexpr -> Prims.bool) =
  fun e  ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_Const uu____1368 -> true
    | FStar_Extraction_ML_Syntax.MLE_Var uu____1369 -> true
    | FStar_Extraction_ML_Syntax.MLE_Name uu____1370 -> true
    | FStar_Extraction_ML_Syntax.MLE_Fun uu____1371 -> true
    | FStar_Extraction_ML_Syntax.MLE_CTor (uu____1382,exps) ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Tuple exps ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Record (uu____1391,fields) ->
        FStar_Util.for_all
          (fun uu____1416  ->
             match uu____1416 with | (uu____1421,e1) -> is_ml_value e1)
          fields
    | FStar_Extraction_ML_Syntax.MLE_TApp (h,uu____1424) -> is_ml_value h
    | uu____1429 -> false
  
let (fresh : Prims.string -> Prims.string) =
  let c = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun x  ->
    FStar_Util.incr c;
    (let uu____1472 =
       let uu____1473 = FStar_ST.op_Bang c  in
       FStar_Util.string_of_int uu____1473  in
     Prims.strcat x uu____1472)
  
let (normalize_abs : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t0  ->
    let rec aux bs t copt =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_abs (bs',body,copt1) ->
          aux (FStar_List.append bs bs') body copt1
      | uu____1588 ->
          let e' = FStar_Syntax_Util.unascribe t1  in
          let uu____1590 = FStar_Syntax_Util.is_fun e'  in
          if uu____1590
          then aux bs e' copt
          else FStar_Syntax_Util.abs bs e' copt
       in
    aux [] t0 FStar_Pervasives_Native.None
  
let (unit_binder : FStar_Syntax_Syntax.binder) =
  let uu____1598 =
    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
      FStar_Syntax_Syntax.t_unit
     in
  FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____1598 
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
      (let uu____1679 = FStar_List.hd l  in
       match uu____1679 with
       | (p1,w1,e1) ->
           let uu____1713 =
             let uu____1722 = FStar_List.tl l  in FStar_List.hd uu____1722
              in
           (match uu____1713 with
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
                 | uu____1796 -> def)))
  
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
      let uu____1833 = FStar_Extraction_ML_Util.doms_and_cod t  in
      match uu____1833 with
      | (ts,r) ->
          if ts = []
          then e
          else
            (let vs = FStar_List.map (fun uu____1853  -> fresh "a") ts  in
             let vs_ts = FStar_List.zip vs ts  in
             let vs_es =
               let uu____1864 = FStar_List.zip vs ts  in
               FStar_List.map
                 (fun uu____1878  ->
                    match uu____1878 with
                    | (v1,t1) ->
                        FStar_Extraction_ML_Syntax.with_ty t1
                          (FStar_Extraction_ML_Syntax.MLE_Var v1)) uu____1864
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
      let uu____1904 = FStar_Extraction_ML_Util.doms_and_cod t  in
      match uu____1904 with
      | (ts,r) ->
          let body r1 =
            let r2 =
              let uu____1924 = FStar_Extraction_ML_Util.udelta_unfold g r1
                 in
              match uu____1924 with
              | FStar_Pervasives_Native.None  -> r1
              | FStar_Pervasives_Native.Some r2 -> r2  in
            match r2 with
            | FStar_Extraction_ML_Syntax.MLTY_Erased  ->
                FStar_Extraction_ML_Syntax.ml_unit
            | FStar_Extraction_ML_Syntax.MLTY_Top  ->
                FStar_Extraction_ML_Syntax.apply_obj_repr
                  FStar_Extraction_ML_Syntax.ml_unit
                  FStar_Extraction_ML_Syntax.MLTY_Erased
            | uu____1928 ->
                FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty r2)
                  (FStar_Extraction_ML_Syntax.MLE_Coerce
                     (FStar_Extraction_ML_Syntax.ml_unit,
                       FStar_Extraction_ML_Syntax.MLTY_Erased, r2))
             in
          if ts = []
          then body r
          else
            (let vs = FStar_List.map (fun uu____1936  -> fresh "a") ts  in
             let vs_ts = FStar_List.zip vs ts  in
             let uu____1944 =
               let uu____1945 =
                 let uu____1956 = body r  in (vs_ts, uu____1956)  in
               FStar_Extraction_ML_Syntax.MLE_Fun uu____1945  in
             FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t)
               uu____1944)
  
let (maybe_eta_expand :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun expect  ->
    fun e  ->
      let uu____1973 =
        (FStar_Options.ml_no_eta_expand_coertions ()) ||
          (let uu____1975 = FStar_Options.codegen ()  in
           uu____1975 = (FStar_Pervasives_Native.Some FStar_Options.Kremlin))
         in
      if uu____1973 then e else eta_expand expect e
  
let maybe_coerce :
  'Auu____1993 .
    'Auu____1993 ->
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
            let uu____2020 =
              type_leq_c g (FStar_Pervasives_Native.Some e) ty1 expect  in
            match uu____2020 with
            | (true ,FStar_Pervasives_Native.Some e') -> e'
            | uu____2030 ->
                (FStar_Extraction_ML_UEnv.debug g
                   (fun uu____2042  ->
                      let uu____2043 =
                        FStar_Extraction_ML_Code.string_of_mlexpr
                          g.FStar_Extraction_ML_UEnv.currentModule e
                         in
                      let uu____2044 =
                        FStar_Extraction_ML_Code.string_of_mlty
                          g.FStar_Extraction_ML_UEnv.currentModule ty1
                         in
                      let uu____2045 =
                        FStar_Extraction_ML_Code.string_of_mlty
                          g.FStar_Extraction_ML_UEnv.currentModule expect
                         in
                      FStar_Util.print3
                        "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n"
                        uu____2043 uu____2044 uu____2045);
                 (match ty1 with
                  | FStar_Extraction_ML_Syntax.MLTY_Erased  ->
                      default_value_for_ty g expect
                  | uu____2046 ->
                      let uu____2047 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty expect)
                          (FStar_Extraction_ML_Syntax.MLE_Coerce
                             (e, ty1, expect))
                         in
                      maybe_eta_expand expect uu____2047))
  
let (bv_as_mlty :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun bv  ->
      let uu____2058 = FStar_Extraction_ML_UEnv.lookup_bv g bv  in
      match uu____2058 with
      | FStar_Util.Inl (uu____2059,t) -> t
      | uu____2073 -> FStar_Extraction_ML_Syntax.MLTY_Top
  
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
      let arg_as_mlty g1 uu____2118 =
        match uu____2118 with
        | (a,uu____2124) ->
            let uu____2125 = is_type g1 a  in
            if uu____2125
            then translate_term_to_mlty g1 a
            else FStar_Extraction_ML_UEnv.erasedContent
         in
      let fv_app_as_mlty g1 fv args =
        let uu____2143 =
          let uu____2144 = FStar_Extraction_ML_UEnv.is_fv_type g1 fv  in
          Prims.op_Negation uu____2144  in
        if uu____2143
        then FStar_Extraction_ML_Syntax.MLTY_Top
        else
          (let uu____2146 =
             let uu____2159 =
               FStar_TypeChecker_Env.lookup_lid
                 g1.FStar_Extraction_ML_UEnv.tcenv
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             match uu____2159 with
             | ((uu____2180,fvty),uu____2182) ->
                 let fvty1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Normalize.UnfoldUntil
                        FStar_Syntax_Syntax.Delta_constant]
                     g1.FStar_Extraction_ML_UEnv.tcenv fvty
                    in
                 FStar_Syntax_Util.arrow_formals fvty1
              in
           match uu____2146 with
           | (formals,uu____2189) ->
               let mlargs = FStar_List.map (arg_as_mlty g1) args  in
               let mlargs1 =
                 let n_args = FStar_List.length args  in
                 if (FStar_List.length formals) > n_args
                 then
                   let uu____2235 = FStar_Util.first_N n_args formals  in
                   match uu____2235 with
                   | (uu____2262,rest) ->
                       let uu____2288 =
                         FStar_List.map
                           (fun uu____2296  ->
                              FStar_Extraction_ML_UEnv.erasedContent) rest
                          in
                       FStar_List.append mlargs uu____2288
                 else mlargs  in
               let nm =
                 let uu____2303 =
                   FStar_Extraction_ML_UEnv.maybe_mangle_type_projector g1 fv
                    in
                 match uu____2303 with
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
        | FStar_Syntax_Syntax.Tm_type uu____2321 ->
            FStar_Extraction_ML_Syntax.MLTY_Erased
        | FStar_Syntax_Syntax.Tm_bvar uu____2322 ->
            let uu____2323 =
              let uu____2324 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____2324
               in
            failwith uu____2323
        | FStar_Syntax_Syntax.Tm_delayed uu____2325 ->
            let uu____2350 =
              let uu____2351 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____2351
               in
            failwith uu____2350
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____2352 =
              let uu____2353 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____2353
               in
            failwith uu____2352
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____2355 = FStar_Syntax_Util.unfold_lazy i  in
            translate_term_to_mlty env uu____2355
        | FStar_Syntax_Syntax.Tm_constant uu____2356 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_quoted uu____2357 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_uvar uu____2364 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_meta (t2,uu____2366) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____2371;
               FStar_Syntax_Syntax.index = uu____2372;
               FStar_Syntax_Syntax.sort = t2;_},uu____2374)
            -> translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_uinst (t2,uu____2382) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____2388,uu____2389) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
        | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv []
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let uu____2456 = FStar_Syntax_Subst.open_comp bs c  in
            (match uu____2456 with
             | (bs1,c1) ->
                 let uu____2463 = binders_as_ml_binders env bs1  in
                 (match uu____2463 with
                  | (mlbs,env1) ->
                      let t_ret =
                        let eff =
                          FStar_TypeChecker_Env.norm_eff_name
                            env1.FStar_Extraction_ML_UEnv.tcenv
                            (FStar_Syntax_Util.comp_effect_name c1)
                           in
                        let uu____2490 =
                          let uu____2497 =
                            FStar_TypeChecker_Env.effect_decl_opt
                              env1.FStar_Extraction_ML_UEnv.tcenv eff
                             in
                          FStar_Util.must uu____2497  in
                        match uu____2490 with
                        | (ed,qualifiers) ->
                            let uu____2518 =
                              FStar_All.pipe_right qualifiers
                                (FStar_List.contains
                                   FStar_Syntax_Syntax.Reifiable)
                               in
                            if uu____2518
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
                      let uu____2525 =
                        FStar_List.fold_right
                          (fun uu____2544  ->
                             fun uu____2545  ->
                               match (uu____2544, uu____2545) with
                               | ((uu____2566,t2),(tag,t')) ->
                                   (FStar_Extraction_ML_Syntax.E_PURE,
                                     (FStar_Extraction_ML_Syntax.MLTY_Fun
                                        (t2, tag, t')))) mlbs (erase, t_ret)
                         in
                      (match uu____2525 with | (uu____2578,t2) -> t2)))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let res =
              let uu____2603 =
                let uu____2604 = FStar_Syntax_Util.un_uinst head1  in
                uu____2604.FStar_Syntax_Syntax.n  in
              match uu____2603 with
              | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv args
              | FStar_Syntax_Syntax.Tm_app (head2,args') ->
                  let uu____2631 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_app
                         (head2, (FStar_List.append args' args)))
                      FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                     in
                  translate_term_to_mlty env uu____2631
              | uu____2648 -> FStar_Extraction_ML_UEnv.unknownType  in
            res
        | FStar_Syntax_Syntax.Tm_abs (bs,ty,uu____2651) ->
            let uu____2672 = FStar_Syntax_Subst.open_term bs ty  in
            (match uu____2672 with
             | (bs1,ty1) ->
                 let uu____2679 = binders_as_ml_binders env bs1  in
                 (match uu____2679 with
                  | (bts,env1) -> translate_term_to_mlty env1 ty1))
        | FStar_Syntax_Syntax.Tm_let uu____2704 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_match uu____2717 ->
            FStar_Extraction_ML_UEnv.unknownType
         in
      let rec is_top_ty t =
        match t with
        | FStar_Extraction_ML_Syntax.MLTY_Top  -> true
        | FStar_Extraction_ML_Syntax.MLTY_Named uu____2746 ->
            let uu____2753 = FStar_Extraction_ML_Util.udelta_unfold g t  in
            (match uu____2753 with
             | FStar_Pervasives_Native.None  -> false
             | FStar_Pervasives_Native.Some t1 -> is_top_ty t1)
        | uu____2757 -> false  in
      let uu____2758 =
        FStar_TypeChecker_Util.must_erase_for_extraction
          g.FStar_Extraction_ML_UEnv.tcenv t0
         in
      if uu____2758
      then FStar_Extraction_ML_Syntax.MLTY_Erased
      else
        (let mlt = aux g t0  in
         let uu____2761 = is_top_ty mlt  in
         if uu____2761
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
      let uu____2776 =
        FStar_All.pipe_right bs
          (FStar_List.fold_left
             (fun uu____2825  ->
                fun b  ->
                  match uu____2825 with
                  | (ml_bs,env) ->
                      let uu____2865 = is_type_binder g b  in
                      if uu____2865
                      then
                        let b1 = FStar_Pervasives_Native.fst b  in
                        let env1 =
                          FStar_Extraction_ML_UEnv.extend_ty env b1
                            (FStar_Pervasives_Native.Some
                               FStar_Extraction_ML_Syntax.MLTY_Top)
                           in
                        let ml_b =
                          let uu____2883 =
                            FStar_Extraction_ML_UEnv.bv_as_ml_termvar b1  in
                          (uu____2883, FStar_Extraction_ML_Syntax.ml_unit_ty)
                           in
                        ((ml_b :: ml_bs), env1)
                      else
                        (let b1 = FStar_Pervasives_Native.fst b  in
                         let t =
                           translate_term_to_mlty env
                             b1.FStar_Syntax_Syntax.sort
                            in
                         let uu____2897 =
                           FStar_Extraction_ML_UEnv.extend_bv env b1 
                             ([], t) false false false
                            in
                         match uu____2897 with
                         | (env1,b2) ->
                             let ml_b =
                               let uu____2919 =
                                 FStar_Extraction_ML_UEnv.removeTick b2  in
                               (uu____2919, t)  in
                             ((ml_b :: ml_bs), env1))) ([], g))
         in
      match uu____2776 with | (ml_bs,env) -> ((FStar_List.rev ml_bs), env)

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
      | (FStar_Extraction_ML_Syntax.MLE_Seq es1,uu____3002) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (FStar_List.append es1 [e2])
      | (uu____3005,FStar_Extraction_ML_Syntax.MLE_Seq es2) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (e1 :: es2)
      | uu____3009 -> FStar_Extraction_ML_Syntax.MLE_Seq [e1; e2]
  
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
                    | uu____3035 when
                        (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
                          =
                          FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr
                        -> body.FStar_Extraction_ML_Syntax.expr
                    | uu____3036 ->
                        mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def
                          body)
             | uu____3037 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body))
        | uu____3046 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body)
  
let (resugar_pat :
  FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option ->
    FStar_Extraction_ML_Syntax.mlpattern ->
      FStar_Extraction_ML_Syntax.mlpattern)
  =
  fun q  ->
    fun p  ->
      match p with
      | FStar_Extraction_ML_Syntax.MLP_CTor (d,pats) ->
          let uu____3073 = FStar_Extraction_ML_Util.is_xtuple d  in
          (match uu____3073 with
           | FStar_Pervasives_Native.Some n1 ->
               FStar_Extraction_ML_Syntax.MLP_Tuple pats
           | uu____3077 ->
               (match q with
                | FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Record_ctor (ty,fns)) ->
                    let path =
                      FStar_List.map FStar_Ident.text_of_id ty.FStar_Ident.ns
                       in
                    let fs = record_fields fns pats  in
                    FStar_Extraction_ML_Syntax.MLP_Record (path, fs)
                | uu____3104 -> p))
      | uu____3107 -> p
  
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
                       (fun uu____3199  ->
                          let uu____3200 =
                            FStar_Extraction_ML_Code.string_of_mlty
                              g.FStar_Extraction_ML_UEnv.currentModule t'
                             in
                          let uu____3201 =
                            FStar_Extraction_ML_Code.string_of_mlty
                              g.FStar_Extraction_ML_UEnv.currentModule t
                             in
                          FStar_Util.print2
                            "Expected pattern type %s; got pattern type %s\n"
                            uu____3200 uu____3201)
                   else ();
                   ok)
               in
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int
                (c,swopt)) when
                let uu____3231 = FStar_Options.codegen ()  in
                uu____3231 <>
                  (FStar_Pervasives_Native.Some FStar_Options.Kremlin)
                ->
                let uu____3236 =
                  match swopt with
                  | FStar_Pervasives_Native.None  ->
                      let uu____3249 =
                        let uu____3250 =
                          let uu____3251 =
                            FStar_Extraction_ML_Util.mlconst_of_const
                              p.FStar_Syntax_Syntax.p
                              (FStar_Const.Const_int
                                 (c, FStar_Pervasives_Native.None))
                             in
                          FStar_Extraction_ML_Syntax.MLE_Const uu____3251  in
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.ml_int_ty) uu____3250
                         in
                      (uu____3249, FStar_Extraction_ML_Syntax.ml_int_ty)
                  | FStar_Pervasives_Native.Some sw ->
                      let source_term =
                        FStar_ToSyntax_ToSyntax.desugar_machine_integer
                          (g.FStar_Extraction_ML_UEnv.tcenv).FStar_TypeChecker_Env.dsenv
                          c sw FStar_Range.dummyRange
                         in
                      let uu____3272 = term_as_mlexpr g source_term  in
                      (match uu____3272 with
                       | (mlterm,uu____3284,mlty) -> (mlterm, mlty))
                   in
                (match uu____3236 with
                 | (mlc,ml_ty) ->
                     let x = FStar_Extraction_ML_Syntax.gensym ()  in
                     let when_clause =
                       let uu____3304 =
                         let uu____3305 =
                           let uu____3312 =
                             let uu____3315 =
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty ml_ty)
                                 (FStar_Extraction_ML_Syntax.MLE_Var x)
                                in
                             [uu____3315; mlc]  in
                           (FStar_Extraction_ML_Util.prims_op_equality,
                             uu____3312)
                            in
                         FStar_Extraction_ML_Syntax.MLE_App uu____3305  in
                       FStar_All.pipe_left
                         (FStar_Extraction_ML_Syntax.with_ty
                            FStar_Extraction_ML_Syntax.ml_bool_ty) uu____3304
                        in
                     let uu____3318 = ok ml_ty  in
                     (g,
                       (FStar_Pervasives_Native.Some
                          ((FStar_Extraction_ML_Syntax.MLP_Var x),
                            [when_clause])), uu____3318))
            | FStar_Syntax_Syntax.Pat_constant s ->
                let t =
                  FStar_TypeChecker_TcTerm.tc_constant
                    g.FStar_Extraction_ML_UEnv.tcenv FStar_Range.dummyRange s
                   in
                let mlty = term_as_mlty g t  in
                let uu____3338 =
                  let uu____3347 =
                    let uu____3354 =
                      let uu____3355 =
                        FStar_Extraction_ML_Util.mlconst_of_const
                          p.FStar_Syntax_Syntax.p s
                         in
                      FStar_Extraction_ML_Syntax.MLP_Const uu____3355  in
                    (uu____3354, [])  in
                  FStar_Pervasives_Native.Some uu____3347  in
                let uu____3364 = ok mlty  in (g, uu____3338, uu____3364)
            | FStar_Syntax_Syntax.Pat_var x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort  in
                let uu____3375 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp
                   in
                (match uu____3375 with
                 | (g1,x1) ->
                     let uu____3396 = ok mlty  in
                     (g1,
                       (if imp
                        then FStar_Pervasives_Native.None
                        else
                          FStar_Pervasives_Native.Some
                            ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                       uu____3396))
            | FStar_Syntax_Syntax.Pat_wild x ->
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
            | FStar_Syntax_Syntax.Pat_dot_term uu____3483 ->
                (g, FStar_Pervasives_Native.None, true)
            | FStar_Syntax_Syntax.Pat_cons (f,pats) ->
                let uu____3522 =
                  let uu____3531 = FStar_Extraction_ML_UEnv.lookup_fv g f  in
                  match uu____3531 with
                  | FStar_Util.Inr
                      (uu____3540,{
                                    FStar_Extraction_ML_Syntax.expr =
                                      FStar_Extraction_ML_Syntax.MLE_Name n1;
                                    FStar_Extraction_ML_Syntax.mlty =
                                      uu____3542;
                                    FStar_Extraction_ML_Syntax.loc =
                                      uu____3543;_},ttys,uu____3545)
                      -> (n1, ttys)
                  | uu____3558 -> failwith "Expected a constructor"  in
                (match uu____3522 with
                 | (d,tys) ->
                     let nTyVars =
                       FStar_List.length (FStar_Pervasives_Native.fst tys)
                        in
                     let uu____3592 = FStar_Util.first_N nTyVars pats  in
                     (match uu____3592 with
                      | (tysVarPats,restPats) ->
                          let f_ty_opt =
                            try
                              let mlty_args =
                                FStar_All.pipe_right tysVarPats
                                  (FStar_List.map
                                     (fun uu____3721  ->
                                        match uu____3721 with
                                        | (p1,uu____3727) ->
                                            (match p1.FStar_Syntax_Syntax.v
                                             with
                                             | FStar_Syntax_Syntax.Pat_dot_term
                                                 (uu____3728,t) ->
                                                 term_as_mlty g t
                                             | uu____3734 ->
                                                 (FStar_Extraction_ML_UEnv.debug
                                                    g
                                                    (fun uu____3738  ->
                                                       let uu____3739 =
                                                         FStar_Syntax_Print.pat_to_string
                                                           p1
                                                          in
                                                       FStar_Util.print1
                                                         "Pattern %s is not extractable"
                                                         uu____3739);
                                                  FStar_Exn.raise
                                                    Un_extractable))))
                                 in
                              let f_ty =
                                FStar_Extraction_ML_Util.subst tys mlty_args
                                 in
                              let uu____3741 =
                                FStar_Extraction_ML_Util.uncurry_mlty_fun
                                  f_ty
                                 in
                              FStar_Pervasives_Native.Some uu____3741
                            with
                            | Un_extractable  -> FStar_Pervasives_Native.None
                             in
                          let uu____3770 =
                            FStar_Util.fold_map
                              (fun g1  ->
                                 fun uu____3806  ->
                                   match uu____3806 with
                                   | (p1,imp1) ->
                                       let uu____3825 =
                                         extract_one_pat true g1 p1
                                           FStar_Pervasives_Native.None
                                           term_as_mlexpr
                                          in
                                       (match uu____3825 with
                                        | (g2,p2,uu____3854) -> (g2, p2))) g
                              tysVarPats
                             in
                          (match uu____3770 with
                           | (g1,tyMLPats) ->
                               let uu____3915 =
                                 FStar_Util.fold_map
                                   (fun uu____3979  ->
                                      fun uu____3980  ->
                                        match (uu____3979, uu____3980) with
                                        | ((g2,f_ty_opt1),(p1,imp1)) ->
                                            let uu____4073 =
                                              match f_ty_opt1 with
                                              | FStar_Pervasives_Native.Some
                                                  (hd1::rest,res) ->
                                                  ((FStar_Pervasives_Native.Some
                                                      (rest, res)),
                                                    (FStar_Pervasives_Native.Some
                                                       hd1))
                                              | uu____4133 ->
                                                  (FStar_Pervasives_Native.None,
                                                    FStar_Pervasives_Native.None)
                                               in
                                            (match uu____4073 with
                                             | (f_ty_opt2,expected_ty) ->
                                                 let uu____4204 =
                                                   extract_one_pat false g2
                                                     p1 expected_ty
                                                     term_as_mlexpr
                                                    in
                                                 (match uu____4204 with
                                                  | (g3,p2,uu____4245) ->
                                                      ((g3, f_ty_opt2), p2))))
                                   (g1, f_ty_opt) restPats
                                  in
                               (match uu____3915 with
                                | ((g2,f_ty_opt1),restMLPats) ->
                                    let uu____4363 =
                                      let uu____4374 =
                                        FStar_All.pipe_right
                                          (FStar_List.append tyMLPats
                                             restMLPats)
                                          (FStar_List.collect
                                             (fun uu___62_4425  ->
                                                match uu___62_4425 with
                                                | FStar_Pervasives_Native.Some
                                                    x -> [x]
                                                | uu____4467 -> []))
                                         in
                                      FStar_All.pipe_right uu____4374
                                        FStar_List.split
                                       in
                                    (match uu____4363 with
                                     | (mlPats,when_clauses) ->
                                         let pat_ty_compat =
                                           match f_ty_opt1 with
                                           | FStar_Pervasives_Native.Some
                                               ([],t) -> ok t
                                           | uu____4540 -> false  in
                                         let uu____4549 =
                                           let uu____4558 =
                                             let uu____4565 =
                                               resugar_pat
                                                 f.FStar_Syntax_Syntax.fv_qual
                                                 (FStar_Extraction_ML_Syntax.MLP_CTor
                                                    (d, mlPats))
                                                in
                                             let uu____4568 =
                                               FStar_All.pipe_right
                                                 when_clauses
                                                 FStar_List.flatten
                                                in
                                             (uu____4565, uu____4568)  in
                                           FStar_Pervasives_Native.Some
                                             uu____4558
                                            in
                                         (g2, uu____4549, pat_ty_compat))))))
  
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
            let uu____4695 =
              extract_one_pat false g1 p1 expected_t1 term_as_mlexpr  in
            match uu____4695 with
            | (g2,FStar_Pervasives_Native.Some (x,v1),b) -> (g2, (x, v1), b)
            | uu____4752 ->
                failwith "Impossible: Unable to translate pattern"
             in
          let mk_when_clause whens =
            match whens with
            | [] -> FStar_Pervasives_Native.None
            | hd1::tl1 ->
                let uu____4797 =
                  FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd1
                    tl1
                   in
                FStar_Pervasives_Native.Some uu____4797
             in
          let uu____4798 =
            extract_one_pat1 g p (FStar_Pervasives_Native.Some expected_t)
             in
          match uu____4798 with
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
            | FStar_Extraction_ML_Syntax.MLTY_Fun (t0,uu____4948,t1) ->
                let x = FStar_Extraction_ML_Syntax.gensym ()  in
                let uu____4951 =
                  let uu____4962 =
                    let uu____4971 =
                      FStar_All.pipe_left
                        (FStar_Extraction_ML_Syntax.with_ty t0)
                        (FStar_Extraction_ML_Syntax.MLE_Var x)
                       in
                    ((x, t0), uu____4971)  in
                  uu____4962 :: more_args  in
                eta_args uu____4951 t1
            | FStar_Extraction_ML_Syntax.MLTY_Named (uu____4984,uu____4985)
                -> ((FStar_List.rev more_args), t)
            | uu____5008 ->
                let uu____5009 =
                  let uu____5010 =
                    FStar_Extraction_ML_Code.string_of_mlexpr
                      g.FStar_Extraction_ML_UEnv.currentModule mlAppExpr
                     in
                  let uu____5011 =
                    FStar_Extraction_ML_Code.string_of_mlty
                      g.FStar_Extraction_ML_UEnv.currentModule t
                     in
                  FStar_Util.format2
                    "Impossible: Head type is not an arrow: (%s : %s)"
                    uu____5010 uu____5011
                   in
                failwith uu____5009
             in
          let as_record qual1 e =
            match ((e.FStar_Extraction_ML_Syntax.expr), qual1) with
            | (FStar_Extraction_ML_Syntax.MLE_CTor
               (uu____5043,args),FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Record_ctor (tyname,fields))) ->
                let path =
                  FStar_List.map FStar_Ident.text_of_id tyname.FStar_Ident.ns
                   in
                let fields1 = record_fields fields args  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     e.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_Record (path, fields1))
            | uu____5075 -> e  in
          let resugar_and_maybe_eta qual1 e =
            let uu____5097 = eta_args [] residualType  in
            match uu____5097 with
            | (eargs,tres) ->
                (match eargs with
                 | [] ->
                     let uu____5150 = as_record qual1 e  in
                     FStar_Extraction_ML_Util.resugar_exp uu____5150
                 | uu____5151 ->
                     let uu____5162 = FStar_List.unzip eargs  in
                     (match uu____5162 with
                      | (binders,eargs1) ->
                          (match e.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_CTor (head1,args)
                               ->
                               let body =
                                 let uu____5204 =
                                   let uu____5205 =
                                     FStar_All.pipe_left
                                       (FStar_Extraction_ML_Syntax.with_ty
                                          tres)
                                       (FStar_Extraction_ML_Syntax.MLE_CTor
                                          (head1,
                                            (FStar_List.append args eargs1)))
                                      in
                                   FStar_All.pipe_left (as_record qual1)
                                     uu____5205
                                    in
                                 FStar_All.pipe_left
                                   FStar_Extraction_ML_Util.resugar_exp
                                   uu____5204
                                  in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    e.FStar_Extraction_ML_Syntax.mlty)
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    (binders, body))
                           | uu____5214 ->
                               failwith "Impossible: Not a constructor")))
             in
          match ((mlAppExpr.FStar_Extraction_ML_Syntax.expr), qual) with
          | (uu____5217,FStar_Pervasives_Native.None ) -> mlAppExpr
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____5221;
                FStar_Extraction_ML_Syntax.loc = uu____5222;_},mle::args),FStar_Pervasives_Native.Some
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
                | uu____5243 ->
                    let uu____5246 =
                      let uu____5253 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj
                         in
                      (uu____5253, args)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____5246
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
                     FStar_Extraction_ML_Syntax.mlty = uu____5257;
                     FStar_Extraction_ML_Syntax.loc = uu____5258;_},uu____5259);
                FStar_Extraction_ML_Syntax.mlty = uu____5260;
                FStar_Extraction_ML_Syntax.loc = uu____5261;_},mle::args),FStar_Pervasives_Native.Some
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
                | uu____5286 ->
                    let uu____5289 =
                      let uu____5296 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj
                         in
                      (uu____5296, args)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____5289
                 in
              FStar_Extraction_ML_Syntax.with_ty
                mlAppExpr.FStar_Extraction_ML_Syntax.mlty e
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____5300;
                FStar_Extraction_ML_Syntax.loc = uu____5301;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____5309 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5309
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____5313;
                FStar_Extraction_ML_Syntax.loc = uu____5314;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____5316)) ->
              let uu____5329 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5329
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____5333;
                     FStar_Extraction_ML_Syntax.loc = uu____5334;_},uu____5335);
                FStar_Extraction_ML_Syntax.mlty = uu____5336;
                FStar_Extraction_ML_Syntax.loc = uu____5337;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____5349 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5349
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____5353;
                     FStar_Extraction_ML_Syntax.loc = uu____5354;_},uu____5355);
                FStar_Extraction_ML_Syntax.mlty = uu____5356;
                FStar_Extraction_ML_Syntax.loc = uu____5357;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____5359)) ->
              let uu____5376 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5376
          | (FStar_Extraction_ML_Syntax.MLE_Name
             mlp,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor
             )) ->
              let uu____5382 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5382
          | (FStar_Extraction_ML_Syntax.MLE_Name
             mlp,FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____5386)) ->
              let uu____5395 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5395
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____5399;
                FStar_Extraction_ML_Syntax.loc = uu____5400;_},uu____5401),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____5408 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5408
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____5412;
                FStar_Extraction_ML_Syntax.loc = uu____5413;_},uu____5414),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____5415)) ->
              let uu____5428 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5428
          | uu____5431 -> mlAppExpr
  
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
        | uu____5461 -> (ml_e, tag)
  
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
            (fun uu____5544  ->
               let uu____5545 = FStar_Syntax_Print.term_to_string e  in
               let uu____5546 =
                 FStar_Extraction_ML_Code.string_of_mlty
                   g.FStar_Extraction_ML_UEnv.currentModule ty
                  in
               FStar_Util.print2 "Checking %s at type %s\n" uu____5545
                 uu____5546);
          (match (f, ty) with
           | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____5551) ->
               (FStar_Extraction_ML_Syntax.ml_unit,
                 FStar_Extraction_ML_Syntax.MLTY_Erased)
           | (FStar_Extraction_ML_Syntax.E_PURE
              ,FStar_Extraction_ML_Syntax.MLTY_Erased ) ->
               (FStar_Extraction_ML_Syntax.ml_unit,
                 FStar_Extraction_ML_Syntax.MLTY_Erased)
           | uu____5552 ->
               let uu____5557 = term_as_mlexpr g e  in
               (match uu____5557 with
                | (ml_e,tag,t) ->
                    let uu____5571 = maybe_promote_effect ml_e tag t  in
                    (match uu____5571 with
                     | (ml_e1,tag1) ->
                         let uu____5582 =
                           FStar_Extraction_ML_Util.eff_leq tag1 f  in
                         if uu____5582
                         then
                           let uu____5587 =
                             maybe_coerce e.FStar_Syntax_Syntax.pos g ml_e1 t
                               ty
                              in
                           (uu____5587, ty)
                         else
                           (match (tag1, f, ty) with
                            | (FStar_Extraction_ML_Syntax.E_GHOST
                               ,FStar_Extraction_ML_Syntax.E_PURE
                               ,FStar_Extraction_ML_Syntax.MLTY_Erased ) ->
                                let uu____5593 =
                                  maybe_coerce e.FStar_Syntax_Syntax.pos g
                                    ml_e1 t ty
                                   in
                                (uu____5593, ty)
                            | uu____5594 ->
                                (err_unexpected_eff g e ty f tag1;
                                 (let uu____5602 =
                                    maybe_coerce e.FStar_Syntax_Syntax.pos g
                                      ml_e1 t ty
                                     in
                                  (uu____5602, ty)))))))

and (term_as_mlexpr :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Extraction_ML_Syntax.mlexpr,FStar_Extraction_ML_Syntax.e_tag,
        FStar_Extraction_ML_Syntax.mlty) FStar_Pervasives_Native.tuple3)
  =
  fun g  ->
    fun e  ->
      let uu____5605 = term_as_mlexpr' g e  in
      match uu____5605 with
      | (e1,f,t) ->
          let uu____5621 = maybe_promote_effect e1 f t  in
          (match uu____5621 with | (e2,f1) -> (e2, f1, t))

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
           let uu____5646 =
             let uu____5647 =
               FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos  in
             let uu____5648 = FStar_Syntax_Print.tag_of_term top  in
             let uu____5649 = FStar_Syntax_Print.term_to_string top  in
             FStar_Util.format3 "%s: term_as_mlexpr' (%s) :  %s \n"
               uu____5647 uu____5648 uu____5649
              in
           FStar_Util.print_string uu____5646);
      (let t = FStar_Syntax_Subst.compress top  in
       match t.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____5657 =
             let uu____5658 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5658
              in
           failwith uu____5657
       | FStar_Syntax_Syntax.Tm_delayed uu____5665 ->
           let uu____5690 =
             let uu____5691 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5691
              in
           failwith uu____5690
       | FStar_Syntax_Syntax.Tm_uvar uu____5698 ->
           let uu____5699 =
             let uu____5700 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5700
              in
           failwith uu____5699
       | FStar_Syntax_Syntax.Tm_bvar uu____5707 ->
           let uu____5708 =
             let uu____5709 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5709
              in
           failwith uu____5708
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____5717 = FStar_Syntax_Util.unfold_lazy i  in
           term_as_mlexpr g uu____5717
       | FStar_Syntax_Syntax.Tm_type uu____5718 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_refine uu____5719 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_arrow uu____5726 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_quoted
           (qt,{
                 FStar_Syntax_Syntax.qkind =
                   FStar_Syntax_Syntax.Quote_dynamic ;
                 FStar_Syntax_Syntax.antiquotes = uu____5740;_})
           ->
           let uu____5755 =
             let uu____5764 =
               let uu____5781 =
                 FStar_Syntax_Syntax.lid_as_fv
                   FStar_Parser_Const.failwith_lid
                   FStar_Syntax_Syntax.Delta_constant
                   FStar_Pervasives_Native.None
                  in
               FStar_Extraction_ML_UEnv.lookup_fv g uu____5781  in
             FStar_All.pipe_left FStar_Util.right uu____5764  in
           (match uu____5755 with
            | (uu____5824,fw,uu____5826,uu____5827) ->
                let uu____5828 =
                  let uu____5829 =
                    let uu____5830 =
                      let uu____5837 =
                        let uu____5840 =
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty
                               FStar_Extraction_ML_Syntax.ml_string_ty)
                            (FStar_Extraction_ML_Syntax.MLE_Const
                               (FStar_Extraction_ML_Syntax.MLC_String
                                  "Open quotation at runtime"))
                           in
                        [uu____5840]  in
                      (fw, uu____5837)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____5830  in
                  FStar_All.pipe_left
                    (FStar_Extraction_ML_Syntax.with_ty
                       FStar_Extraction_ML_Syntax.ml_int_ty) uu____5829
                   in
                (uu____5828, FStar_Extraction_ML_Syntax.E_PURE,
                  FStar_Extraction_ML_Syntax.ml_int_ty))
       | FStar_Syntax_Syntax.Tm_quoted
           (qt,{
                 FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static ;
                 FStar_Syntax_Syntax.antiquotes = aqs;_})
           ->
           let uu____5859 = FStar_Reflection_Basic.inspect_ln qt  in
           (match uu____5859 with
            | FStar_Reflection_Data.Tv_Var bv ->
                let uu____5867 = FStar_Syntax_Syntax.lookup_aq bv aqs  in
                (match uu____5867 with
                 | FStar_Pervasives_Native.Some (false ,tm) ->
                     term_as_mlexpr g tm
                 | FStar_Pervasives_Native.Some (true ,tm) ->
                     let uu____5890 =
                       let uu____5899 =
                         let uu____5916 =
                           FStar_Syntax_Syntax.lid_as_fv
                             FStar_Parser_Const.failwith_lid
                             FStar_Syntax_Syntax.Delta_constant
                             FStar_Pervasives_Native.None
                            in
                         FStar_Extraction_ML_UEnv.lookup_fv g uu____5916  in
                       FStar_All.pipe_left FStar_Util.right uu____5899  in
                     (match uu____5890 with
                      | (uu____5959,fw,uu____5961,uu____5962) ->
                          let uu____5963 =
                            let uu____5964 =
                              let uu____5965 =
                                let uu____5972 =
                                  let uu____5975 =
                                    FStar_All.pipe_left
                                      (FStar_Extraction_ML_Syntax.with_ty
                                         FStar_Extraction_ML_Syntax.ml_string_ty)
                                      (FStar_Extraction_ML_Syntax.MLE_Const
                                         (FStar_Extraction_ML_Syntax.MLC_String
                                            "Open quotation at runtime"))
                                     in
                                  [uu____5975]  in
                                (fw, uu____5972)  in
                              FStar_Extraction_ML_Syntax.MLE_App uu____5965
                               in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.ml_int_ty)
                              uu____5964
                             in
                          (uu____5963, FStar_Extraction_ML_Syntax.E_PURE,
                            FStar_Extraction_ML_Syntax.ml_int_ty))
                 | FStar_Pervasives_Native.None  ->
                     let tv =
                       let uu____5983 =
                         FStar_Reflection_Embeddings.e_term_view_aq aqs  in
                       FStar_Syntax_Embeddings.embed uu____5983
                         t.FStar_Syntax_Syntax.pos
                         (FStar_Reflection_Data.Tv_Var bv)
                        in
                     let t1 =
                       let uu____5989 =
                         let uu____5998 = FStar_Syntax_Syntax.as_arg tv  in
                         [uu____5998]  in
                       FStar_Syntax_Util.mk_app
                         (FStar_Reflection_Data.refl_constant_term
                            FStar_Reflection_Data.fstar_refl_pack_ln)
                         uu____5989
                        in
                     term_as_mlexpr g t1)
            | tv ->
                let tv1 =
                  let uu____6019 =
                    FStar_Reflection_Embeddings.e_term_view_aq aqs  in
                  FStar_Syntax_Embeddings.embed uu____6019
                    t.FStar_Syntax_Syntax.pos tv
                   in
                let t1 =
                  let uu____6025 =
                    let uu____6034 = FStar_Syntax_Syntax.as_arg tv1  in
                    [uu____6034]  in
                  FStar_Syntax_Util.mk_app
                    (FStar_Reflection_Data.refl_constant_term
                       FStar_Reflection_Data.fstar_refl_pack_ln) uu____6025
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
           (t1,FStar_Syntax_Syntax.Meta_monadic (m,uu____6066)) ->
           let t2 = FStar_Syntax_Subst.compress t1  in
           (match t2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) when
                FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname ->
                let uu____6096 =
                  let uu____6103 =
                    FStar_TypeChecker_Env.effect_decl_opt
                      g.FStar_Extraction_ML_UEnv.tcenv m
                     in
                  FStar_Util.must uu____6103  in
                (match uu____6096 with
                 | (ed,qualifiers) ->
                     let uu____6130 =
                       let uu____6131 =
                         FStar_All.pipe_right qualifiers
                           (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                          in
                       FStar_All.pipe_right uu____6131 Prims.op_Negation  in
                     if uu____6130
                     then term_as_mlexpr g t2
                     else
                       failwith
                         "This should not happen (should have been handled at Tm_abs level)")
            | uu____6147 -> term_as_mlexpr g t2)
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____6149) -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____6155) -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____6161 =
             FStar_TypeChecker_TcTerm.type_of_tot_term
               g.FStar_Extraction_ML_UEnv.tcenv t
              in
           (match uu____6161 with
            | (uu____6174,ty,uu____6176) ->
                let ml_ty = term_as_mlty g ty  in
                let uu____6178 =
                  let uu____6179 =
                    FStar_Extraction_ML_Util.mlexpr_of_const
                      t.FStar_Syntax_Syntax.pos c
                     in
                  FStar_Extraction_ML_Syntax.with_ty ml_ty uu____6179  in
                (uu____6178, FStar_Extraction_ML_Syntax.E_PURE, ml_ty))
       | FStar_Syntax_Syntax.Tm_name uu____6180 ->
           let uu____6181 = is_type g t  in
           if uu____6181
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____6189 = FStar_Extraction_ML_UEnv.lookup_term g t  in
              match uu____6189 with
              | (FStar_Util.Inl uu____6202,uu____6203) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | (FStar_Util.Inr (uu____6224,x,mltys,uu____6227),qual) ->
                  (match mltys with
                   | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                       ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | ([],t1) ->
                       let uu____6253 =
                         maybe_eta_data_and_project_record g qual t1 x  in
                       (uu____6253, FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | uu____6254 -> err_uninst g t mltys t))
       | FStar_Syntax_Syntax.Tm_fvar fv ->
           let uu____6262 = is_type g t  in
           if uu____6262
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____6270 = FStar_Extraction_ML_UEnv.try_lookup_fv g fv
                 in
              match uu____6270 with
              | FStar_Pervasives_Native.None  ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.MLTY_Erased)
              | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____6279) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | FStar_Pervasives_Native.Some (FStar_Util.Inr
                  (uu____6296,x,mltys,uu____6299)) ->
                  (match mltys with
                   | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                       ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | ([],t1) ->
                       let uu____6320 =
                         maybe_eta_data_and_project_record g
                           fv.FStar_Syntax_Syntax.fv_qual t1 x
                          in
                       (uu____6320, FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | uu____6321 -> err_uninst g t mltys t))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,copt) ->
           let uu____6351 = FStar_Syntax_Subst.open_term bs body  in
           (match uu____6351 with
            | (bs1,body1) ->
                let uu____6364 = binders_as_ml_binders g bs1  in
                (match uu____6364 with
                 | (ml_bs,env) ->
                     let body2 =
                       match copt with
                       | FStar_Pervasives_Native.Some c ->
                           let uu____6397 =
                             FStar_TypeChecker_Env.is_reifiable
                               env.FStar_Extraction_ML_UEnv.tcenv c
                              in
                           if uu____6397
                           then
                             FStar_TypeChecker_Util.reify_body
                               env.FStar_Extraction_ML_UEnv.tcenv body1
                           else body1
                       | FStar_Pervasives_Native.None  ->
                           (FStar_Extraction_ML_UEnv.debug g
                              (fun uu____6402  ->
                                 let uu____6403 =
                                   FStar_Syntax_Print.term_to_string body1
                                    in
                                 FStar_Util.print1
                                   "No computation type for: %s\n" uu____6403);
                            body1)
                        in
                     let uu____6404 = term_as_mlexpr env body2  in
                     (match uu____6404 with
                      | (ml_body,f,t1) ->
                          let uu____6420 =
                            FStar_List.fold_right
                              (fun uu____6439  ->
                                 fun uu____6440  ->
                                   match (uu____6439, uu____6440) with
                                   | ((uu____6461,targ),(f1,t2)) ->
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         (FStar_Extraction_ML_Syntax.MLTY_Fun
                                            (targ, f1, t2)))) ml_bs (f, t1)
                             in
                          (match uu____6420 with
                           | (f1,tfun) ->
                               let uu____6481 =
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty tfun)
                                   (FStar_Extraction_ML_Syntax.MLE_Fun
                                      (ml_bs, ml_body))
                                  in
                               (uu____6481, f1, tfun)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____6488;
              FStar_Syntax_Syntax.vars = uu____6489;_},(a1,uu____6491)::[])
           ->
           let ty =
             let uu____6521 =
               FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid  in
             term_as_mlty g uu____6521  in
           let uu____6522 =
             let uu____6523 =
               FStar_Extraction_ML_Util.mlexpr_of_range
                 a1.FStar_Syntax_Syntax.pos
                in
             FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty)
               uu____6523
              in
           (uu____6522, FStar_Extraction_ML_Syntax.E_PURE, ty)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____6524;
              FStar_Syntax_Syntax.vars = uu____6525;_},(t1,uu____6527)::
            (r,uu____6529)::[])
           -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____6568);
              FStar_Syntax_Syntax.pos = uu____6569;
              FStar_Syntax_Syntax.vars = uu____6570;_},uu____6571)
           -> failwith "Unreachable? Tm_app Const_reflect"
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let is_total rc =
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_Tot_lid)
               ||
               (FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
                  (FStar_List.existsb
                     (fun uu___63_6629  ->
                        match uu___63_6629 with
                        | FStar_Syntax_Syntax.TOTAL  -> true
                        | uu____6630 -> false)))
              in
           let uu____6631 =
             let uu____6636 =
               let uu____6637 = FStar_Syntax_Subst.compress head1  in
               uu____6637.FStar_Syntax_Syntax.n  in
             ((head1.FStar_Syntax_Syntax.n), uu____6636)  in
           (match uu____6631 with
            | (FStar_Syntax_Syntax.Tm_uvar uu____6646,uu____6647) ->
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
            | (uu____6649,FStar_Syntax_Syntax.Tm_abs
               (bs,uu____6651,FStar_Pervasives_Native.Some rc)) when
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
            | (uu____6672,FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_reify )) ->
                let e =
                  let uu____6674 = FStar_List.hd args  in
                  FStar_TypeChecker_Util.reify_body_with_arg
                    g.FStar_Extraction_ML_UEnv.tcenv head1 uu____6674
                   in
                let tm =
                  let uu____6684 =
                    let uu____6689 = FStar_TypeChecker_Util.remove_reify e
                       in
                    let uu____6690 = FStar_List.tl args  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____6689 uu____6690  in
                  uu____6684 FStar_Pervasives_Native.None
                    t.FStar_Syntax_Syntax.pos
                   in
                term_as_mlexpr g tm
            | uu____6699 ->
                let rec extract_app is_data uu____6752 uu____6753 restArgs =
                  match (uu____6752, uu____6753) with
                  | ((mlhead,mlargs_f),(f,t1)) ->
                      (match (restArgs, t1) with
                       | ([],uu____6845) ->
                           let mlargs =
                             FStar_All.pipe_right (FStar_List.rev mlargs_f)
                               (FStar_List.map FStar_Pervasives_Native.fst)
                              in
                           let app =
                             let uu____6884 =
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty t1)
                                 (FStar_Extraction_ML_Syntax.MLE_App
                                    (mlhead, mlargs))
                                in
                             FStar_All.pipe_left
                               (maybe_eta_data_and_project_record g is_data
                                  t1) uu____6884
                              in
                           (app, f, t1)
                       | ((arg,uu____6888)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                          (formal_t,f',t2)) when
                           (is_type g arg) &&
                             (type_leq g formal_t
                                FStar_Extraction_ML_Syntax.ml_unit_ty)
                           ->
                           let uu____6929 =
                             let uu____6934 =
                               FStar_Extraction_ML_Util.join
                                 arg.FStar_Syntax_Syntax.pos f f'
                                in
                             (uu____6934, t2)  in
                           extract_app is_data
                             (mlhead,
                               ((FStar_Extraction_ML_Syntax.ml_unit,
                                  FStar_Extraction_ML_Syntax.E_PURE) ::
                               mlargs_f)) uu____6929 rest
                       | ((e0,uu____6946)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                          (tExpected,f',t2)) ->
                           let r = e0.FStar_Syntax_Syntax.pos  in
                           let expected_effect =
                             let uu____6989 =
                               (FStar_Options.lax ()) &&
                                 (FStar_TypeChecker_Util.short_circuit_head
                                    head1)
                                in
                             if uu____6989
                             then FStar_Extraction_ML_Syntax.E_IMPURE
                             else FStar_Extraction_ML_Syntax.E_PURE  in
                           let uu____6991 =
                             check_term_as_mlexpr g e0 expected_effect
                               tExpected
                              in
                           (match uu____6991 with
                            | (e01,tInferred) ->
                                let uu____7004 =
                                  let uu____7009 =
                                    FStar_Extraction_ML_Util.join_l r [f; f']
                                     in
                                  (uu____7009, t2)  in
                                extract_app is_data
                                  (mlhead, ((e01, expected_effect) ::
                                    mlargs_f)) uu____7004 rest)
                       | uu____7020 ->
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
                let extract_app_maybe_projector is_data mlhead uu____7105
                  args1 =
                  match uu____7105 with
                  | (f,t1) ->
                      (match is_data with
                       | FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_projector uu____7135)
                           ->
                           let rec remove_implicits args2 f1 t2 =
                             match (args2, t2) with
                             | ((a0,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____7219))::args3,FStar_Extraction_ML_Syntax.MLTY_Fun
                                (uu____7221,f',t3)) ->
                                 let uu____7258 =
                                   FStar_Extraction_ML_Util.join
                                     a0.FStar_Syntax_Syntax.pos f1 f'
                                    in
                                 remove_implicits args3 uu____7258 t3
                             | uu____7259 -> (args2, f1, t2)  in
                           let uu____7284 = remove_implicits args1 f t1  in
                           (match uu____7284 with
                            | (args2,f1,t2) ->
                                extract_app is_data (mlhead, []) (f1, t2)
                                  args2)
                       | uu____7340 ->
                           extract_app is_data (mlhead, []) (f, t1) args1)
                   in
                let extract_app_with_instantiations uu____7364 =
                  let head2 = FStar_Syntax_Util.un_uinst head1  in
                  match head2.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_name uu____7372 ->
                      let uu____7373 =
                        let uu____7392 =
                          FStar_Extraction_ML_UEnv.lookup_term g head2  in
                        match uu____7392 with
                        | (FStar_Util.Inr (uu____7417,x1,x2,x3),q) ->
                            ((x1, x2, x3), q)
                        | uu____7446 -> failwith "FIXME Ty"  in
                      (match uu____7373 with
                       | ((head_ml,(vars,t1),inst_ok),qual) ->
                           let has_typ_apps =
                             match args with
                             | (a,uu____7510)::uu____7511 -> is_type g a
                             | uu____7530 -> false  in
                           let uu____7539 =
                             match vars with
                             | uu____7568::uu____7569 when
                                 (Prims.op_Negation has_typ_apps) && inst_ok
                                 -> (head_ml, t1, args)
                             | uu____7580 ->
                                 let n1 = FStar_List.length vars  in
                                 if n1 <= (FStar_List.length args)
                                 then
                                   let uu____7610 =
                                     FStar_Util.first_N n1 args  in
                                   (match uu____7610 with
                                    | (prefix1,rest) ->
                                        let prefixAsMLTypes =
                                          FStar_List.map
                                            (fun uu____7699  ->
                                               match uu____7699 with
                                               | (x,uu____7705) ->
                                                   term_as_mlty g x) prefix1
                                           in
                                        let t2 =
                                          instantiate (vars, t1)
                                            prefixAsMLTypes
                                           in
                                        let mk_tapp e ty_args =
                                          match ty_args with
                                          | [] -> e
                                          | uu____7722 ->
                                              let uu___67_7725 = e  in
                                              {
                                                FStar_Extraction_ML_Syntax.expr
                                                  =
                                                  (FStar_Extraction_ML_Syntax.MLE_TApp
                                                     (e, ty_args));
                                                FStar_Extraction_ML_Syntax.mlty
                                                  =
                                                  (uu___67_7725.FStar_Extraction_ML_Syntax.mlty);
                                                FStar_Extraction_ML_Syntax.loc
                                                  =
                                                  (uu___67_7725.FStar_Extraction_ML_Syntax.loc)
                                              }
                                           in
                                        let head3 =
                                          match head_ml.FStar_Extraction_ML_Syntax.expr
                                          with
                                          | FStar_Extraction_ML_Syntax.MLE_Name
                                              uu____7729 ->
                                              let uu___68_7730 =
                                                mk_tapp head_ml
                                                  prefixAsMLTypes
                                                 in
                                              {
                                                FStar_Extraction_ML_Syntax.expr
                                                  =
                                                  (uu___68_7730.FStar_Extraction_ML_Syntax.expr);
                                                FStar_Extraction_ML_Syntax.mlty
                                                  = t2;
                                                FStar_Extraction_ML_Syntax.loc
                                                  =
                                                  (uu___68_7730.FStar_Extraction_ML_Syntax.loc)
                                              }
                                          | FStar_Extraction_ML_Syntax.MLE_Var
                                              uu____7731 ->
                                              let uu___68_7732 =
                                                mk_tapp head_ml
                                                  prefixAsMLTypes
                                                 in
                                              {
                                                FStar_Extraction_ML_Syntax.expr
                                                  =
                                                  (uu___68_7732.FStar_Extraction_ML_Syntax.expr);
                                                FStar_Extraction_ML_Syntax.mlty
                                                  = t2;
                                                FStar_Extraction_ML_Syntax.loc
                                                  =
                                                  (uu___68_7732.FStar_Extraction_ML_Syntax.loc)
                                              }
                                          | FStar_Extraction_ML_Syntax.MLE_App
                                              (head3,{
                                                       FStar_Extraction_ML_Syntax.expr
                                                         =
                                                         FStar_Extraction_ML_Syntax.MLE_Const
                                                         (FStar_Extraction_ML_Syntax.MLC_Unit
                                                         );
                                                       FStar_Extraction_ML_Syntax.mlty
                                                         = uu____7734;
                                                       FStar_Extraction_ML_Syntax.loc
                                                         = uu____7735;_}::[])
                                              ->
                                              FStar_All.pipe_right
                                                (FStar_Extraction_ML_Syntax.MLE_App
                                                   ((let uu___69_7741 =
                                                       mk_tapp head3
                                                         prefixAsMLTypes
                                                        in
                                                     {
                                                       FStar_Extraction_ML_Syntax.expr
                                                         =
                                                         (uu___69_7741.FStar_Extraction_ML_Syntax.expr);
                                                       FStar_Extraction_ML_Syntax.mlty
                                                         =
                                                         (FStar_Extraction_ML_Syntax.MLTY_Fun
                                                            (FStar_Extraction_ML_Syntax.ml_unit_ty,
                                                              FStar_Extraction_ML_Syntax.E_PURE,
                                                              t2));
                                                       FStar_Extraction_ML_Syntax.loc
                                                         =
                                                         (uu___69_7741.FStar_Extraction_ML_Syntax.loc)
                                                     }),
                                                     [FStar_Extraction_ML_Syntax.ml_unit]))
                                                (FStar_Extraction_ML_Syntax.with_ty
                                                   t2)
                                          | uu____7742 ->
                                              failwith
                                                "Impossible: Unexpected head term"
                                           in
                                        (head3, t2, rest))
                                 else err_uninst g head2 (vars, t1) top
                              in
                           (match uu____7539 with
                            | (head_ml1,head_t,args1) ->
                                (match args1 with
                                 | [] ->
                                     let uu____7805 =
                                       maybe_eta_data_and_project_record g
                                         qual head_t head_ml1
                                        in
                                     (uu____7805,
                                       FStar_Extraction_ML_Syntax.E_PURE,
                                       head_t)
                                 | uu____7806 ->
                                     extract_app_maybe_projector qual
                                       head_ml1
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         head_t) args1)))
                  | FStar_Syntax_Syntax.Tm_fvar uu____7815 ->
                      let uu____7816 =
                        let uu____7835 =
                          FStar_Extraction_ML_UEnv.lookup_term g head2  in
                        match uu____7835 with
                        | (FStar_Util.Inr (uu____7860,x1,x2,x3),q) ->
                            ((x1, x2, x3), q)
                        | uu____7889 -> failwith "FIXME Ty"  in
                      (match uu____7816 with
                       | ((head_ml,(vars,t1),inst_ok),qual) ->
                           let has_typ_apps =
                             match args with
                             | (a,uu____7953)::uu____7954 -> is_type g a
                             | uu____7973 -> false  in
                           let uu____7982 =
                             match vars with
                             | uu____8011::uu____8012 when
                                 (Prims.op_Negation has_typ_apps) && inst_ok
                                 -> (head_ml, t1, args)
                             | uu____8023 ->
                                 let n1 = FStar_List.length vars  in
                                 if n1 <= (FStar_List.length args)
                                 then
                                   let uu____8053 =
                                     FStar_Util.first_N n1 args  in
                                   (match uu____8053 with
                                    | (prefix1,rest) ->
                                        let prefixAsMLTypes =
                                          FStar_List.map
                                            (fun uu____8142  ->
                                               match uu____8142 with
                                               | (x,uu____8148) ->
                                                   term_as_mlty g x) prefix1
                                           in
                                        let t2 =
                                          instantiate (vars, t1)
                                            prefixAsMLTypes
                                           in
                                        let mk_tapp e ty_args =
                                          match ty_args with
                                          | [] -> e
                                          | uu____8165 ->
                                              let uu___67_8168 = e  in
                                              {
                                                FStar_Extraction_ML_Syntax.expr
                                                  =
                                                  (FStar_Extraction_ML_Syntax.MLE_TApp
                                                     (e, ty_args));
                                                FStar_Extraction_ML_Syntax.mlty
                                                  =
                                                  (uu___67_8168.FStar_Extraction_ML_Syntax.mlty);
                                                FStar_Extraction_ML_Syntax.loc
                                                  =
                                                  (uu___67_8168.FStar_Extraction_ML_Syntax.loc)
                                              }
                                           in
                                        let head3 =
                                          match head_ml.FStar_Extraction_ML_Syntax.expr
                                          with
                                          | FStar_Extraction_ML_Syntax.MLE_Name
                                              uu____8172 ->
                                              let uu___68_8173 =
                                                mk_tapp head_ml
                                                  prefixAsMLTypes
                                                 in
                                              {
                                                FStar_Extraction_ML_Syntax.expr
                                                  =
                                                  (uu___68_8173.FStar_Extraction_ML_Syntax.expr);
                                                FStar_Extraction_ML_Syntax.mlty
                                                  = t2;
                                                FStar_Extraction_ML_Syntax.loc
                                                  =
                                                  (uu___68_8173.FStar_Extraction_ML_Syntax.loc)
                                              }
                                          | FStar_Extraction_ML_Syntax.MLE_Var
                                              uu____8174 ->
                                              let uu___68_8175 =
                                                mk_tapp head_ml
                                                  prefixAsMLTypes
                                                 in
                                              {
                                                FStar_Extraction_ML_Syntax.expr
                                                  =
                                                  (uu___68_8175.FStar_Extraction_ML_Syntax.expr);
                                                FStar_Extraction_ML_Syntax.mlty
                                                  = t2;
                                                FStar_Extraction_ML_Syntax.loc
                                                  =
                                                  (uu___68_8175.FStar_Extraction_ML_Syntax.loc)
                                              }
                                          | FStar_Extraction_ML_Syntax.MLE_App
                                              (head3,{
                                                       FStar_Extraction_ML_Syntax.expr
                                                         =
                                                         FStar_Extraction_ML_Syntax.MLE_Const
                                                         (FStar_Extraction_ML_Syntax.MLC_Unit
                                                         );
                                                       FStar_Extraction_ML_Syntax.mlty
                                                         = uu____8177;
                                                       FStar_Extraction_ML_Syntax.loc
                                                         = uu____8178;_}::[])
                                              ->
                                              FStar_All.pipe_right
                                                (FStar_Extraction_ML_Syntax.MLE_App
                                                   ((let uu___69_8184 =
                                                       mk_tapp head3
                                                         prefixAsMLTypes
                                                        in
                                                     {
                                                       FStar_Extraction_ML_Syntax.expr
                                                         =
                                                         (uu___69_8184.FStar_Extraction_ML_Syntax.expr);
                                                       FStar_Extraction_ML_Syntax.mlty
                                                         =
                                                         (FStar_Extraction_ML_Syntax.MLTY_Fun
                                                            (FStar_Extraction_ML_Syntax.ml_unit_ty,
                                                              FStar_Extraction_ML_Syntax.E_PURE,
                                                              t2));
                                                       FStar_Extraction_ML_Syntax.loc
                                                         =
                                                         (uu___69_8184.FStar_Extraction_ML_Syntax.loc)
                                                     }),
                                                     [FStar_Extraction_ML_Syntax.ml_unit]))
                                                (FStar_Extraction_ML_Syntax.with_ty
                                                   t2)
                                          | uu____8185 ->
                                              failwith
                                                "Impossible: Unexpected head term"
                                           in
                                        (head3, t2, rest))
                                 else err_uninst g head2 (vars, t1) top
                              in
                           (match uu____7982 with
                            | (head_ml1,head_t,args1) ->
                                (match args1 with
                                 | [] ->
                                     let uu____8248 =
                                       maybe_eta_data_and_project_record g
                                         qual head_t head_ml1
                                        in
                                     (uu____8248,
                                       FStar_Extraction_ML_Syntax.E_PURE,
                                       head_t)
                                 | uu____8249 ->
                                     extract_app_maybe_projector qual
                                       head_ml1
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         head_t) args1)))
                  | uu____8258 ->
                      let uu____8259 = term_as_mlexpr g head2  in
                      (match uu____8259 with
                       | (head3,f,t1) ->
                           extract_app_maybe_projector
                             FStar_Pervasives_Native.None head3 (f, t1) args)
                   in
                let uu____8275 = is_type g t  in
                if uu____8275
                then
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
                else
                  (let uu____8283 =
                     let uu____8284 = FStar_Syntax_Util.un_uinst head1  in
                     uu____8284.FStar_Syntax_Syntax.n  in
                   match uu____8283 with
                   | FStar_Syntax_Syntax.Tm_fvar fv ->
                       let uu____8294 =
                         FStar_Extraction_ML_UEnv.try_lookup_fv g fv  in
                       (match uu____8294 with
                        | FStar_Pervasives_Native.None  ->
                            (FStar_Extraction_ML_Syntax.ml_unit,
                              FStar_Extraction_ML_Syntax.E_PURE,
                              FStar_Extraction_ML_Syntax.MLTY_Erased)
                        | uu____8303 -> extract_app_with_instantiations ())
                   | uu____8306 -> extract_app_with_instantiations ()))
       | FStar_Syntax_Syntax.Tm_ascribed (e0,(tc,uu____8309),f) ->
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
           let uu____8376 = check_term_as_mlexpr g e0 f1 t1  in
           (match uu____8376 with | (e,t2) -> (e, f1, t2))
       | FStar_Syntax_Syntax.Tm_let ((is_rec,lbs),e') ->
           let top_level = FStar_Syntax_Syntax.is_top_level lbs  in
           let uu____8407 =
             if is_rec
             then FStar_Syntax_Subst.open_let_rec lbs e'
             else
               (let uu____8421 = FStar_Syntax_Syntax.is_top_level lbs  in
                if uu____8421
                then (lbs, e')
                else
                  (let lb = FStar_List.hd lbs  in
                   let x =
                     let uu____8435 =
                       FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                     FStar_Syntax_Syntax.freshen_bv uu____8435  in
                   let lb1 =
                     let uu___70_8437 = lb  in
                     {
                       FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                       FStar_Syntax_Syntax.lbunivs =
                         (uu___70_8437.FStar_Syntax_Syntax.lbunivs);
                       FStar_Syntax_Syntax.lbtyp =
                         (uu___70_8437.FStar_Syntax_Syntax.lbtyp);
                       FStar_Syntax_Syntax.lbeff =
                         (uu___70_8437.FStar_Syntax_Syntax.lbeff);
                       FStar_Syntax_Syntax.lbdef =
                         (uu___70_8437.FStar_Syntax_Syntax.lbdef);
                       FStar_Syntax_Syntax.lbattrs =
                         (uu___70_8437.FStar_Syntax_Syntax.lbattrs);
                       FStar_Syntax_Syntax.lbpos =
                         (uu___70_8437.FStar_Syntax_Syntax.lbpos)
                     }  in
                   let e'1 =
                     FStar_Syntax_Subst.subst
                       [FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x)] e'
                      in
                   ([lb1], e'1)))
              in
           (match uu____8407 with
            | (lbs1,e'1) ->
                let lbs2 =
                  if top_level
                  then
                    FStar_All.pipe_right lbs1
                      (FStar_List.map
                         (fun lb  ->
                            let tcenv =
                              let uu____8468 =
                                FStar_Ident.lid_of_path
                                  (FStar_List.append
                                     (FStar_Pervasives_Native.fst
                                        g.FStar_Extraction_ML_UEnv.currentModule)
                                     [FStar_Pervasives_Native.snd
                                        g.FStar_Extraction_ML_UEnv.currentModule])
                                  FStar_Range.dummyRange
                                 in
                              FStar_TypeChecker_Env.set_current_module
                                g.FStar_Extraction_ML_UEnv.tcenv uu____8468
                               in
                            let lbdef =
                              let uu____8476 = FStar_Options.ml_ish ()  in
                              if uu____8476
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
                            let uu___71_8480 = lb  in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___71_8480.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___71_8480.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp =
                                (uu___71_8480.FStar_Syntax_Syntax.lbtyp);
                              FStar_Syntax_Syntax.lbeff =
                                (uu___71_8480.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = lbdef;
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___71_8480.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___71_8480.FStar_Syntax_Syntax.lbpos)
                            }))
                  else lbs1  in
                let maybe_generalize uu____8487 =
                  match uu____8487 with
                  | { FStar_Syntax_Syntax.lbname = lbname_;
                      FStar_Syntax_Syntax.lbunivs = uu____8489;
                      FStar_Syntax_Syntax.lbtyp = t1;
                      FStar_Syntax_Syntax.lbeff = lbeff;
                      FStar_Syntax_Syntax.lbdef = e;
                      FStar_Syntax_Syntax.lbattrs = uu____8493;
                      FStar_Syntax_Syntax.lbpos = uu____8494;_} ->
                      let f_e = effect_as_etag g lbeff  in
                      let t2 = FStar_Syntax_Subst.compress t1  in
                      let no_gen uu____8552 =
                        let expected_t = term_as_mlty g t2  in
                        (lbname_, f_e, (t2, ([], ([], expected_t))), false,
                          e)
                         in
                      let uu____8614 =
                        FStar_TypeChecker_Util.must_erase_for_extraction
                          g.FStar_Extraction_ML_UEnv.tcenv t2
                         in
                      if uu____8614
                      then
                        (lbname_, f_e,
                          (t2,
                            ([],
                              ([], FStar_Extraction_ML_Syntax.MLTY_Erased))),
                          false, e)
                      else
                        (match t2.FStar_Syntax_Syntax.n with
                         | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                             let uu____8650 = FStar_List.hd bs  in
                             FStar_All.pipe_right uu____8650
                               (is_type_binder g)
                             ->
                             let uu____8663 =
                               FStar_Syntax_Subst.open_comp bs c  in
                             (match uu____8663 with
                              | (bs1,c1) ->
                                  let uu____8670 =
                                    let uu____8677 =
                                      FStar_Util.prefix_until
                                        (fun x  ->
                                           let uu____8713 =
                                             is_type_binder g x  in
                                           Prims.op_Negation uu____8713) bs1
                                       in
                                    match uu____8677 with
                                    | FStar_Pervasives_Native.None  ->
                                        (bs1,
                                          (FStar_Syntax_Util.comp_result c1))
                                    | FStar_Pervasives_Native.Some
                                        (bs2,b,rest) ->
                                        let uu____8801 =
                                          FStar_Syntax_Util.arrow (b :: rest)
                                            c1
                                           in
                                        (bs2, uu____8801)
                                     in
                                  (match uu____8670 with
                                   | (tbinders,tbody) ->
                                       let n_tbinders =
                                         FStar_List.length tbinders  in
                                       let e1 =
                                         let uu____8830 = normalize_abs e  in
                                         FStar_All.pipe_right uu____8830
                                           FStar_Syntax_Util.unmeta
                                          in
                                       (match e1.FStar_Syntax_Syntax.n with
                                        | FStar_Syntax_Syntax.Tm_abs
                                            (bs2,body,copt) ->
                                            let uu____8856 =
                                              FStar_Syntax_Subst.open_term
                                                bs2 body
                                               in
                                            (match uu____8856 with
                                             | (bs3,body1) ->
                                                 if
                                                   n_tbinders <=
                                                     (FStar_List.length bs3)
                                                 then
                                                   let uu____8873 =
                                                     FStar_Util.first_N
                                                       n_tbinders bs3
                                                      in
                                                   (match uu____8873 with
                                                    | (targs,rest_args) ->
                                                        let expected_source_ty
                                                          =
                                                          let s =
                                                            FStar_List.map2
                                                              (fun uu____8943
                                                                  ->
                                                                 fun
                                                                   uu____8944
                                                                    ->
                                                                   match 
                                                                    (uu____8943,
                                                                    uu____8944)
                                                                   with
                                                                   | 
                                                                   ((x,uu____8962),
                                                                    (y,uu____8964))
                                                                    ->
                                                                    let uu____8973
                                                                    =
                                                                    let uu____8980
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    y  in
                                                                    (x,
                                                                    uu____8980)
                                                                     in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____8973)
                                                              tbinders targs
                                                             in
                                                          FStar_Syntax_Subst.subst
                                                            s tbody
                                                           in
                                                        let env =
                                                          FStar_List.fold_left
                                                            (fun env  ->
                                                               fun uu____8995
                                                                  ->
                                                                 match uu____8995
                                                                 with
                                                                 | (a,uu____9001)
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
                                                          let uu____9008 =
                                                            FStar_All.pipe_right
                                                              targs
                                                              (FStar_List.map
                                                                 (fun
                                                                    uu____9022
                                                                     ->
                                                                    match uu____9022
                                                                    with
                                                                    | 
                                                                    (x,uu____9028)
                                                                    ->
                                                                    FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                                    x))
                                                             in
                                                          (uu____9008,
                                                            expected_t)
                                                           in
                                                        let add_unit =
                                                          match rest_args
                                                          with
                                                          | [] ->
                                                              (let uu____9036
                                                                 =
                                                                 is_fstar_value
                                                                   body1
                                                                  in
                                                               Prims.op_Negation
                                                                 uu____9036)
                                                                ||
                                                                (let uu____9038
                                                                   =
                                                                   FStar_Syntax_Util.is_pure_comp
                                                                    c1
                                                                    in
                                                                 Prims.op_Negation
                                                                   uu____9038)
                                                          | uu____9039 ->
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
                                            uu____9070 ->
                                            let env =
                                              FStar_List.fold_left
                                                (fun env  ->
                                                   fun uu____9087  ->
                                                     match uu____9087 with
                                                     | (a,uu____9093) ->
                                                         FStar_Extraction_ML_UEnv.extend_ty
                                                           env a
                                                           FStar_Pervasives_Native.None)
                                                g tbinders
                                               in
                                            let expected_t =
                                              term_as_mlty env tbody  in
                                            let polytype =
                                              let uu____9100 =
                                                FStar_All.pipe_right tbinders
                                                  (FStar_List.map
                                                     (fun uu____9114  ->
                                                        match uu____9114 with
                                                        | (x,uu____9120) ->
                                                            FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                              x))
                                                 in
                                              (uu____9100, expected_t)  in
                                            let args =
                                              FStar_All.pipe_right tbinders
                                                (FStar_List.map
                                                   (fun uu____9152  ->
                                                      match uu____9152 with
                                                      | (bv,uu____9158) ->
                                                          let uu____9159 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              bv
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____9159
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
                                            uu____9185 ->
                                            let env =
                                              FStar_List.fold_left
                                                (fun env  ->
                                                   fun uu____9196  ->
                                                     match uu____9196 with
                                                     | (a,uu____9202) ->
                                                         FStar_Extraction_ML_UEnv.extend_ty
                                                           env a
                                                           FStar_Pervasives_Native.None)
                                                g tbinders
                                               in
                                            let expected_t =
                                              term_as_mlty env tbody  in
                                            let polytype =
                                              let uu____9209 =
                                                FStar_All.pipe_right tbinders
                                                  (FStar_List.map
                                                     (fun uu____9223  ->
                                                        match uu____9223 with
                                                        | (x,uu____9229) ->
                                                            FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                              x))
                                                 in
                                              (uu____9209, expected_t)  in
                                            let args =
                                              FStar_All.pipe_right tbinders
                                                (FStar_List.map
                                                   (fun uu____9261  ->
                                                      match uu____9261 with
                                                      | (bv,uu____9267) ->
                                                          let uu____9268 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              bv
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____9268
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
                                            uu____9294 ->
                                            let env =
                                              FStar_List.fold_left
                                                (fun env  ->
                                                   fun uu____9305  ->
                                                     match uu____9305 with
                                                     | (a,uu____9311) ->
                                                         FStar_Extraction_ML_UEnv.extend_ty
                                                           env a
                                                           FStar_Pervasives_Native.None)
                                                g tbinders
                                               in
                                            let expected_t =
                                              term_as_mlty env tbody  in
                                            let polytype =
                                              let uu____9318 =
                                                FStar_All.pipe_right tbinders
                                                  (FStar_List.map
                                                     (fun uu____9332  ->
                                                        match uu____9332 with
                                                        | (x,uu____9338) ->
                                                            FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                              x))
                                                 in
                                              (uu____9318, expected_t)  in
                                            let args =
                                              FStar_All.pipe_right tbinders
                                                (FStar_List.map
                                                   (fun uu____9370  ->
                                                      match uu____9370 with
                                                      | (bv,uu____9376) ->
                                                          let uu____9377 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              bv
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____9377
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
                                        | uu____9403 ->
                                            err_value_restriction e1)))
                         | uu____9404 -> no_gen ())
                   in
                let check_lb env uu____9423 =
                  match uu____9423 with
                  | (nm,(_lbname,f,(_t,(targs,polytype)),add_unit,e)) ->
                      let env1 =
                        FStar_List.fold_left
                          (fun env1  ->
                             fun uu____9462  ->
                               match uu____9462 with
                               | (a,uu____9468) ->
                                   FStar_Extraction_ML_UEnv.extend_ty env1 a
                                     FStar_Pervasives_Native.None) env targs
                         in
                      let expected_t = FStar_Pervasives_Native.snd polytype
                         in
                      let uu____9470 =
                        check_term_as_mlexpr env1 e f expected_t  in
                      (match uu____9470 with
                       | (e1,ty) ->
                           let uu____9481 =
                             maybe_promote_effect e1 f expected_t  in
                           (match uu____9481 with
                            | (e2,f1) ->
                                let meta =
                                  match (f1, ty) with
                                  | (FStar_Extraction_ML_Syntax.E_PURE
                                     ,FStar_Extraction_ML_Syntax.MLTY_Erased
                                     ) -> [FStar_Extraction_ML_Syntax.Erased]
                                  | (FStar_Extraction_ML_Syntax.E_GHOST
                                     ,FStar_Extraction_ML_Syntax.MLTY_Erased
                                     ) -> [FStar_Extraction_ML_Syntax.Erased]
                                  | uu____9493 -> []  in
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
                let uu____9541 =
                  FStar_List.fold_right
                    (fun lb  ->
                       fun uu____9632  ->
                         match uu____9632 with
                         | (env,lbs4) ->
                             let uu____9757 = lb  in
                             (match uu____9757 with
                              | (lbname,uu____9805,(t1,(uu____9807,polytype)),add_unit,uu____9810)
                                  ->
                                  let uu____9823 =
                                    FStar_Extraction_ML_UEnv.extend_lb env
                                      lbname t1 polytype add_unit true
                                     in
                                  (match uu____9823 with
                                   | (env1,nm) -> (env1, ((nm, lb) :: lbs4)))))
                    lbs3 (g, [])
                   in
                (match uu____9541 with
                 | (env_body,lbs4) ->
                     let env_def = if is_rec then env_body else g  in
                     let lbs5 =
                       FStar_All.pipe_right lbs4
                         (FStar_List.map (check_lb env_def))
                        in
                     let e'_rng = e'1.FStar_Syntax_Syntax.pos  in
                     let uu____10054 = term_as_mlexpr env_body e'1  in
                     (match uu____10054 with
                      | (e'2,f',t') ->
                          let f =
                            let uu____10071 =
                              let uu____10074 =
                                FStar_List.map FStar_Pervasives_Native.fst
                                  lbs5
                                 in
                              f' :: uu____10074  in
                            FStar_Extraction_ML_Util.join_l e'_rng
                              uu____10071
                             in
                          let is_rec1 =
                            if is_rec = true
                            then FStar_Extraction_ML_Syntax.Rec
                            else FStar_Extraction_ML_Syntax.NonRec  in
                          let uu____10083 =
                            let uu____10084 =
                              let uu____10085 =
                                let uu____10086 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    lbs5
                                   in
                                (is_rec1, uu____10086)  in
                              mk_MLE_Let top_level uu____10085 e'2  in
                            let uu____10095 =
                              FStar_Extraction_ML_Util.mlloc_of_range
                                t.FStar_Syntax_Syntax.pos
                               in
                            FStar_Extraction_ML_Syntax.with_ty_loc t'
                              uu____10084 uu____10095
                             in
                          (uu____10083, f, t'))))
       | FStar_Syntax_Syntax.Tm_match (scrutinee,pats) ->
           let uu____10134 = term_as_mlexpr g scrutinee  in
           (match uu____10134 with
            | (e,f_e,t_e) ->
                let uu____10150 = check_pats_for_ite pats  in
                (match uu____10150 with
                 | (b,then_e,else_e) ->
                     let no_lift x t1 = x  in
                     if b
                     then
                       (match (then_e, else_e) with
                        | (FStar_Pervasives_Native.Some
                           then_e1,FStar_Pervasives_Native.Some else_e1) ->
                            let uu____10211 = term_as_mlexpr g then_e1  in
                            (match uu____10211 with
                             | (then_mle,f_then,t_then) ->
                                 let uu____10227 = term_as_mlexpr g else_e1
                                    in
                                 (match uu____10227 with
                                  | (else_mle,f_else,t_else) ->
                                      let uu____10243 =
                                        let uu____10254 =
                                          type_leq g t_then t_else  in
                                        if uu____10254
                                        then (t_else, no_lift)
                                        else
                                          (let uu____10272 =
                                             type_leq g t_else t_then  in
                                           if uu____10272
                                           then (t_then, no_lift)
                                           else
                                             (FStar_Extraction_ML_Syntax.MLTY_Top,
                                               FStar_Extraction_ML_Syntax.apply_obj_repr))
                                         in
                                      (match uu____10243 with
                                       | (t_branch,maybe_lift1) ->
                                           let uu____10316 =
                                             let uu____10317 =
                                               let uu____10318 =
                                                 let uu____10327 =
                                                   maybe_lift1 then_mle
                                                     t_then
                                                    in
                                                 let uu____10328 =
                                                   let uu____10331 =
                                                     maybe_lift1 else_mle
                                                       t_else
                                                      in
                                                   FStar_Pervasives_Native.Some
                                                     uu____10331
                                                    in
                                                 (e, uu____10327,
                                                   uu____10328)
                                                  in
                                               FStar_Extraction_ML_Syntax.MLE_If
                                                 uu____10318
                                                in
                                             FStar_All.pipe_left
                                               (FStar_Extraction_ML_Syntax.with_ty
                                                  t_branch) uu____10317
                                              in
                                           let uu____10334 =
                                             FStar_Extraction_ML_Util.join
                                               then_e1.FStar_Syntax_Syntax.pos
                                               f_then f_else
                                              in
                                           (uu____10316, uu____10334,
                                             t_branch))))
                        | uu____10335 ->
                            failwith
                              "ITE pats matched but then and else expressions not found?")
                     else
                       (let uu____10351 =
                          FStar_All.pipe_right pats
                            (FStar_Util.fold_map
                               (fun compat  ->
                                  fun br  ->
                                    let uu____10446 =
                                      FStar_Syntax_Subst.open_branch br  in
                                    match uu____10446 with
                                    | (pat,when_opt,branch1) ->
                                        let uu____10490 =
                                          extract_pat g pat t_e
                                            term_as_mlexpr
                                           in
                                        (match uu____10490 with
                                         | (env,p,pat_t_compat) ->
                                             let uu____10548 =
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
                                                   let uu____10571 =
                                                     term_as_mlexpr env w  in
                                                   (match uu____10571 with
                                                    | (w1,f_w,t_w) ->
                                                        let w2 =
                                                          maybe_coerce w_pos
                                                            env w1 t_w
                                                            FStar_Extraction_ML_Syntax.ml_bool_ty
                                                           in
                                                        ((FStar_Pervasives_Native.Some
                                                            w2), f_w))
                                                in
                                             (match uu____10548 with
                                              | (when_opt1,f_when) ->
                                                  let uu____10620 =
                                                    term_as_mlexpr env
                                                      branch1
                                                     in
                                                  (match uu____10620 with
                                                   | (mlbranch,f_branch,t_branch)
                                                       ->
                                                       let uu____10654 =
                                                         FStar_All.pipe_right
                                                           p
                                                           (FStar_List.map
                                                              (fun
                                                                 uu____10731 
                                                                 ->
                                                                 match uu____10731
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
                                                         uu____10654)))))
                               true)
                           in
                        match uu____10351 with
                        | (pat_t_compat,mlbranches) ->
                            let mlbranches1 = FStar_List.flatten mlbranches
                               in
                            let e1 =
                              if pat_t_compat
                              then e
                              else
                                (FStar_Extraction_ML_UEnv.debug g
                                   (fun uu____10896  ->
                                      let uu____10897 =
                                        FStar_Extraction_ML_Code.string_of_mlexpr
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          e
                                         in
                                      let uu____10898 =
                                        FStar_Extraction_ML_Code.string_of_mlty
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          t_e
                                         in
                                      FStar_Util.print2
                                        "Coercing scrutinee %s from type %s because pattern type is incompatible\n"
                                        uu____10897 uu____10898);
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty t_e)
                                   (FStar_Extraction_ML_Syntax.MLE_Coerce
                                      (e, t_e,
                                        FStar_Extraction_ML_Syntax.MLTY_Top)))
                               in
                            (match mlbranches1 with
                             | [] ->
                                 let uu____10923 =
                                   let uu____10932 =
                                     let uu____10949 =
                                       FStar_Syntax_Syntax.lid_as_fv
                                         FStar_Parser_Const.failwith_lid
                                         FStar_Syntax_Syntax.Delta_constant
                                         FStar_Pervasives_Native.None
                                        in
                                     FStar_Extraction_ML_UEnv.lookup_fv g
                                       uu____10949
                                      in
                                   FStar_All.pipe_left FStar_Util.right
                                     uu____10932
                                    in
                                 (match uu____10923 with
                                  | (uu____10992,fw,uu____10994,uu____10995)
                                      ->
                                      let uu____10996 =
                                        let uu____10997 =
                                          let uu____10998 =
                                            let uu____11005 =
                                              let uu____11008 =
                                                FStar_All.pipe_left
                                                  (FStar_Extraction_ML_Syntax.with_ty
                                                     FStar_Extraction_ML_Syntax.ml_string_ty)
                                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                                     (FStar_Extraction_ML_Syntax.MLC_String
                                                        "unreachable"))
                                                 in
                                              [uu____11008]  in
                                            (fw, uu____11005)  in
                                          FStar_Extraction_ML_Syntax.MLE_App
                                            uu____10998
                                           in
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             FStar_Extraction_ML_Syntax.ml_int_ty)
                                          uu____10997
                                         in
                                      (uu____10996,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        FStar_Extraction_ML_Syntax.ml_int_ty))
                             | (uu____11011,uu____11012,(uu____11013,f_first,t_first))::rest
                                 ->
                                 let uu____11073 =
                                   FStar_List.fold_left
                                     (fun uu____11115  ->
                                        fun uu____11116  ->
                                          match (uu____11115, uu____11116)
                                          with
                                          | ((topt,f),(uu____11173,uu____11174,
                                                       (uu____11175,f_branch,t_branch)))
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
                                                    let uu____11231 =
                                                      type_leq g t1 t_branch
                                                       in
                                                    if uu____11231
                                                    then
                                                      FStar_Pervasives_Native.Some
                                                        t_branch
                                                    else
                                                      (let uu____11235 =
                                                         type_leq g t_branch
                                                           t1
                                                          in
                                                       if uu____11235
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
                                 (match uu____11073 with
                                  | (topt,f_match) ->
                                      let mlbranches2 =
                                        FStar_All.pipe_right mlbranches1
                                          (FStar_List.map
                                             (fun uu____11330  ->
                                                match uu____11330 with
                                                | (p,(wopt,uu____11359),
                                                   (b1,uu____11361,t1)) ->
                                                    let b2 =
                                                      match topt with
                                                      | FStar_Pervasives_Native.None
                                                           ->
                                                          FStar_Extraction_ML_Syntax.apply_obj_repr
                                                            b1 t1
                                                      | FStar_Pervasives_Native.Some
                                                          uu____11380 -> b1
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
                                      let uu____11385 =
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             t_match)
                                          (FStar_Extraction_ML_Syntax.MLE_Match
                                             (e1, mlbranches2))
                                         in
                                      (uu____11385, f_match, t_match)))))))

let (ind_discriminator_body :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlmodule1)
  =
  fun env  ->
    fun discName  ->
      fun constrName  ->
        let uu____11411 =
          let uu____11416 =
            FStar_TypeChecker_Env.lookup_lid
              env.FStar_Extraction_ML_UEnv.tcenv discName
             in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____11416  in
        match uu____11411 with
        | (uu____11441,fstar_disc_type) ->
            let wildcards =
              let uu____11450 =
                let uu____11451 = FStar_Syntax_Subst.compress fstar_disc_type
                   in
                uu____11451.FStar_Syntax_Syntax.n  in
              match uu____11450 with
              | FStar_Syntax_Syntax.Tm_arrow (binders,uu____11461) ->
                  let uu____11478 =
                    FStar_All.pipe_right binders
                      (FStar_List.filter
                         (fun uu___64_11512  ->
                            match uu___64_11512 with
                            | (uu____11519,FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____11520)) ->
                                true
                            | uu____11523 -> false))
                     in
                  FStar_All.pipe_right uu____11478
                    (FStar_List.map
                       (fun uu____11556  ->
                          let uu____11563 = fresh "_"  in
                          (uu____11563, FStar_Extraction_ML_Syntax.MLTY_Top)))
              | uu____11564 -> failwith "Discriminator must be a function"
               in
            let mlid = fresh "_discr_"  in
            let targ = FStar_Extraction_ML_Syntax.MLTY_Top  in
            let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top  in
            let discrBody =
              let uu____11575 =
                let uu____11576 =
                  let uu____11587 =
                    let uu____11588 =
                      let uu____11589 =
                        let uu____11604 =
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty targ)
                            (FStar_Extraction_ML_Syntax.MLE_Name ([], mlid))
                           in
                        let uu____11607 =
                          let uu____11618 =
                            let uu____11627 =
                              let uu____11628 =
                                let uu____11635 =
                                  FStar_Extraction_ML_Syntax.mlpath_of_lident
                                    constrName
                                   in
                                (uu____11635,
                                  [FStar_Extraction_ML_Syntax.MLP_Wild])
                                 in
                              FStar_Extraction_ML_Syntax.MLP_CTor uu____11628
                               in
                            let uu____11638 =
                              FStar_All.pipe_left
                                (FStar_Extraction_ML_Syntax.with_ty
                                   FStar_Extraction_ML_Syntax.ml_bool_ty)
                                (FStar_Extraction_ML_Syntax.MLE_Const
                                   (FStar_Extraction_ML_Syntax.MLC_Bool true))
                               in
                            (uu____11627, FStar_Pervasives_Native.None,
                              uu____11638)
                             in
                          let uu____11641 =
                            let uu____11652 =
                              let uu____11661 =
                                FStar_All.pipe_left
                                  (FStar_Extraction_ML_Syntax.with_ty
                                     FStar_Extraction_ML_Syntax.ml_bool_ty)
                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                     (FStar_Extraction_ML_Syntax.MLC_Bool
                                        false))
                                 in
                              (FStar_Extraction_ML_Syntax.MLP_Wild,
                                FStar_Pervasives_Native.None, uu____11661)
                               in
                            [uu____11652]  in
                          uu____11618 :: uu____11641  in
                        (uu____11604, uu____11607)  in
                      FStar_Extraction_ML_Syntax.MLE_Match uu____11589  in
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.ml_bool_ty) uu____11588
                     in
                  ((FStar_List.append wildcards [(mlid, targ)]), uu____11587)
                   in
                FStar_Extraction_ML_Syntax.MLE_Fun uu____11576  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty disc_ty) uu____11575
               in
            let uu____11716 =
              let uu____11717 =
                let uu____11720 =
                  let uu____11721 =
                    FStar_Extraction_ML_UEnv.convIdent
                      discName.FStar_Ident.ident
                     in
                  {
                    FStar_Extraction_ML_Syntax.mllb_name = uu____11721;
                    FStar_Extraction_ML_Syntax.mllb_tysc =
                      FStar_Pervasives_Native.None;
                    FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                    FStar_Extraction_ML_Syntax.mllb_def = discrBody;
                    FStar_Extraction_ML_Syntax.mllb_meta = [];
                    FStar_Extraction_ML_Syntax.print_typ = false
                  }  in
                [uu____11720]  in
              (FStar_Extraction_ML_Syntax.NonRec, uu____11717)  in
            FStar_Extraction_ML_Syntax.MLM_Let uu____11716
  