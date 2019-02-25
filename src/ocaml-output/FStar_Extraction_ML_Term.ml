open Prims
exception Un_extractable 
let (uu___is_Un_extractable : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Un_extractable  -> true | uu____70647 -> false
  
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
  'Auu____70716 .
    FStar_Ident.ident Prims.list ->
      'Auu____70716 Prims.list -> (Prims.string * 'Auu____70716) Prims.list
  =
  fun fs  ->
    fun vs  ->
      FStar_List.map2 (fun f  -> fun e  -> ((f.FStar_Ident.idText), e)) fs vs
  
let fail :
  'Auu____70759 .
    FStar_Range.range ->
      (FStar_Errors.raw_error * Prims.string) -> 'Auu____70759
  = fun r  -> fun err  -> FStar_Errors.raise_error err r 
let err_uninst :
  'Auu____70791 .
    FStar_Extraction_ML_UEnv.uenv ->
      FStar_Syntax_Syntax.term ->
        (Prims.string Prims.list * FStar_Extraction_ML_Syntax.mlty) ->
          FStar_Syntax_Syntax.term -> 'Auu____70791
  =
  fun env  ->
    fun t  ->
      fun uu____70817  ->
        fun app  ->
          match uu____70817 with
          | (vars,ty) ->
              let uu____70834 =
                let uu____70840 =
                  let uu____70842 = FStar_Syntax_Print.term_to_string t  in
                  let uu____70844 =
                    FStar_All.pipe_right vars (FStar_String.concat ", ")  in
                  let uu____70851 =
                    FStar_Extraction_ML_Code.string_of_mlty
                      env.FStar_Extraction_ML_UEnv.currentModule ty
                     in
                  let uu____70853 = FStar_Syntax_Print.term_to_string app  in
                  FStar_Util.format4
                    "Variable %s has a polymorphic type (forall %s. %s); expected it to be fully instantiated, but got %s"
                    uu____70842 uu____70844 uu____70851 uu____70853
                   in
                (FStar_Errors.Fatal_Uninstantiated, uu____70840)  in
              fail t.FStar_Syntax_Syntax.pos uu____70834
  
let err_ill_typed_application :
  'Auu____70872 'Auu____70873 .
    FStar_Extraction_ML_UEnv.uenv ->
      FStar_Syntax_Syntax.term ->
        FStar_Extraction_ML_Syntax.mlexpr ->
          (FStar_Syntax_Syntax.term * 'Auu____70872) Prims.list ->
            FStar_Extraction_ML_Syntax.mlty -> 'Auu____70873
  =
  fun env  ->
    fun t  ->
      fun mlhead  ->
        fun args  ->
          fun ty  ->
            let uu____70911 =
              let uu____70917 =
                let uu____70919 = FStar_Syntax_Print.term_to_string t  in
                let uu____70921 =
                  FStar_Extraction_ML_Code.string_of_mlexpr
                    env.FStar_Extraction_ML_UEnv.currentModule mlhead
                   in
                let uu____70923 =
                  FStar_Extraction_ML_Code.string_of_mlty
                    env.FStar_Extraction_ML_UEnv.currentModule ty
                   in
                let uu____70925 =
                  let uu____70927 =
                    FStar_All.pipe_right args
                      (FStar_List.map
                         (fun uu____70948  ->
                            match uu____70948 with
                            | (x,uu____70955) ->
                                FStar_Syntax_Print.term_to_string x))
                     in
                  FStar_All.pipe_right uu____70927 (FStar_String.concat " ")
                   in
                FStar_Util.format4
                  "Ill-typed application: source application is %s \n translated prefix to %s at type %s\n remaining args are %s\n"
                  uu____70919 uu____70921 uu____70923 uu____70925
                 in
              (FStar_Errors.Fatal_IllTyped, uu____70917)  in
            fail t.FStar_Syntax_Syntax.pos uu____70911
  
let err_ill_typed_erasure :
  'Auu____70972 .
    FStar_Extraction_ML_UEnv.uenv ->
      FStar_Range.range -> FStar_Extraction_ML_Syntax.mlty -> 'Auu____70972
  =
  fun env  ->
    fun pos  ->
      fun ty  ->
        let uu____70988 =
          let uu____70994 =
            let uu____70996 =
              FStar_Extraction_ML_Code.string_of_mlty
                env.FStar_Extraction_ML_UEnv.currentModule ty
               in
            FStar_Util.format1
              "Erased value found where a value of type %s was expected"
              uu____70996
             in
          (FStar_Errors.Fatal_IllTyped, uu____70994)  in
        fail pos uu____70988
  
let err_value_restriction :
  'Auu____71005 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> 'Auu____71005
  =
  fun t  ->
    let uu____71015 =
      let uu____71021 =
        let uu____71023 = FStar_Syntax_Print.tag_of_term t  in
        let uu____71025 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format2
          "Refusing to generalize because of the value restriction: (%s) %s"
          uu____71023 uu____71025
         in
      (FStar_Errors.Fatal_ValueRestriction, uu____71021)  in
    fail t.FStar_Syntax_Syntax.pos uu____71015
  
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
            let uu____71059 =
              let uu____71065 =
                let uu____71067 = FStar_Syntax_Print.term_to_string t  in
                let uu____71069 =
                  FStar_Extraction_ML_Code.string_of_mlty
                    env.FStar_Extraction_ML_UEnv.currentModule ty
                   in
                let uu____71071 = FStar_Extraction_ML_Util.eff_to_string f0
                   in
                let uu____71073 = FStar_Extraction_ML_Util.eff_to_string f1
                   in
                FStar_Util.format4
                  "for expression %s of type %s, Expected effect %s; got effect %s"
                  uu____71067 uu____71069 uu____71071 uu____71073
                 in
              (FStar_Errors.Warning_ExtractionUnexpectedEffect, uu____71065)
               in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____71059
  
let (effect_as_etag :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Ident.lident -> FStar_Extraction_ML_Syntax.e_tag)
  =
  let cache = FStar_Util.smap_create (Prims.parse_int "20")  in
  let rec delta_norm_eff g l =
    let uu____71101 = FStar_Util.smap_try_find cache l.FStar_Ident.str  in
    match uu____71101 with
    | FStar_Pervasives_Native.Some l1 -> l1
    | FStar_Pervasives_Native.None  ->
        let res =
          let uu____71106 =
            FStar_TypeChecker_Env.lookup_effect_abbrev
              g.FStar_Extraction_ML_UEnv.env_tcenv
              [FStar_Syntax_Syntax.U_zero] l
             in
          match uu____71106 with
          | FStar_Pervasives_Native.None  -> l
          | FStar_Pervasives_Native.Some (uu____71117,c) ->
              delta_norm_eff g (FStar_Syntax_Util.comp_effect_name c)
           in
        (FStar_Util.smap_add cache l.FStar_Ident.str res; res)
     in
  fun g  ->
    fun l  ->
      let l1 = delta_norm_eff g l  in
      let uu____71127 =
        FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid  in
      if uu____71127
      then FStar_Extraction_ML_Syntax.E_PURE
      else
        (let uu____71132 =
           FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GHOST_lid  in
         if uu____71132
         then FStar_Extraction_ML_Syntax.E_GHOST
         else
           (let ed_opt =
              FStar_TypeChecker_Env.effect_decl_opt
                g.FStar_Extraction_ML_UEnv.env_tcenv l1
               in
            match ed_opt with
            | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                let uu____71158 =
                  FStar_TypeChecker_Env.is_reifiable_effect
                    g.FStar_Extraction_ML_UEnv.env_tcenv
                    ed.FStar_Syntax_Syntax.mname
                   in
                if uu____71158
                then FStar_Extraction_ML_Syntax.E_PURE
                else FStar_Extraction_ML_Syntax.E_IMPURE
            | FStar_Pervasives_Native.None  ->
                FStar_Extraction_ML_Syntax.E_IMPURE))
  
let rec (is_arity :
  FStar_Extraction_ML_UEnv.uenv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t  in
      let uu____71182 =
        let uu____71183 = FStar_Syntax_Subst.compress t1  in
        uu____71183.FStar_Syntax_Syntax.n  in
      match uu____71182 with
      | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____71189 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_ascribed uu____71214 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_meta uu____71243 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____71253 = FStar_Syntax_Util.unfold_lazy i  in
          is_arity env uu____71253
      | FStar_Syntax_Syntax.Tm_uvar uu____71254 -> false
      | FStar_Syntax_Syntax.Tm_constant uu____71268 -> false
      | FStar_Syntax_Syntax.Tm_name uu____71270 -> false
      | FStar_Syntax_Syntax.Tm_quoted uu____71272 -> false
      | FStar_Syntax_Syntax.Tm_bvar uu____71280 -> false
      | FStar_Syntax_Syntax.Tm_type uu____71282 -> true
      | FStar_Syntax_Syntax.Tm_arrow (uu____71284,c) ->
          is_arity env (FStar_Syntax_Util.comp_result c)
      | FStar_Syntax_Syntax.Tm_fvar uu____71306 ->
          let t2 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Env.AllowUnboundUniverses;
              FStar_TypeChecker_Env.EraseUniverses;
              FStar_TypeChecker_Env.UnfoldUntil
                FStar_Syntax_Syntax.delta_constant]
              env.FStar_Extraction_ML_UEnv.env_tcenv t1
             in
          let uu____71308 =
            let uu____71309 = FStar_Syntax_Subst.compress t2  in
            uu____71309.FStar_Syntax_Syntax.n  in
          (match uu____71308 with
           | FStar_Syntax_Syntax.Tm_fvar uu____71313 -> false
           | uu____71315 -> is_arity env t2)
      | FStar_Syntax_Syntax.Tm_app uu____71316 ->
          let uu____71333 = FStar_Syntax_Util.head_and_args t1  in
          (match uu____71333 with | (head1,uu____71352) -> is_arity env head1)
      | FStar_Syntax_Syntax.Tm_uinst (head1,uu____71378) ->
          is_arity env head1
      | FStar_Syntax_Syntax.Tm_refine (x,uu____71384) ->
          is_arity env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_abs (uu____71389,body,uu____71391) ->
          is_arity env body
      | FStar_Syntax_Syntax.Tm_let (uu____71416,body) -> is_arity env body
      | FStar_Syntax_Syntax.Tm_match (uu____71436,branches) ->
          (match branches with
           | (uu____71475,uu____71476,e)::uu____71478 -> is_arity env e
           | uu____71525 -> false)
  
let rec (is_type_aux :
  FStar_Extraction_ML_UEnv.uenv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____71557 ->
          let uu____71580 =
            let uu____71582 = FStar_Syntax_Print.tag_of_term t1  in
            FStar_Util.format1 "Impossible: %s" uu____71582  in
          failwith uu____71580
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____71586 =
            let uu____71588 = FStar_Syntax_Print.tag_of_term t1  in
            FStar_Util.format1 "Impossible: %s" uu____71588  in
          failwith uu____71586
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____71593 = FStar_Syntax_Util.unfold_lazy i  in
          is_type_aux env uu____71593
      | FStar_Syntax_Syntax.Tm_constant uu____71594 -> false
      | FStar_Syntax_Syntax.Tm_type uu____71596 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____71598 -> true
      | FStar_Syntax_Syntax.Tm_arrow uu____71606 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.failwith_lid ->
          false
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Extraction_ML_UEnv.is_type_name env fv
      | FStar_Syntax_Syntax.Tm_uvar
          ({ FStar_Syntax_Syntax.ctx_uvar_head = uu____71625;
             FStar_Syntax_Syntax.ctx_uvar_gamma = uu____71626;
             FStar_Syntax_Syntax.ctx_uvar_binders = uu____71627;
             FStar_Syntax_Syntax.ctx_uvar_typ = t2;
             FStar_Syntax_Syntax.ctx_uvar_reason = uu____71629;
             FStar_Syntax_Syntax.ctx_uvar_should_check = uu____71630;
             FStar_Syntax_Syntax.ctx_uvar_range = uu____71631;
             FStar_Syntax_Syntax.ctx_uvar_meta = uu____71632;_},s)
          ->
          let uu____71681 = FStar_Syntax_Subst.subst' s t2  in
          is_arity env uu____71681
      | FStar_Syntax_Syntax.Tm_bvar
          { FStar_Syntax_Syntax.ppname = uu____71682;
            FStar_Syntax_Syntax.index = uu____71683;
            FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_name
          { FStar_Syntax_Syntax.ppname = uu____71688;
            FStar_Syntax_Syntax.index = uu____71689;
            FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____71695,uu____71696) ->
          is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____71738) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____71745) ->
          let uu____71770 = FStar_Syntax_Subst.open_term bs body  in
          (match uu____71770 with
           | (uu____71776,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
          let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
          let uu____71796 =
            let uu____71801 =
              let uu____71802 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____71802]  in
            FStar_Syntax_Subst.open_term uu____71801 body  in
          (match uu____71796 with
           | (uu____71822,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_let ((uu____71824,lbs),body) ->
          let uu____71844 = FStar_Syntax_Subst.open_let_rec lbs body  in
          (match uu____71844 with
           | (uu____71852,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_match (uu____71858,branches) ->
          (match branches with
           | b::uu____71898 ->
               let uu____71943 = FStar_Syntax_Subst.open_branch b  in
               (match uu____71943 with
                | (uu____71945,uu____71946,e) -> is_type_aux env e)
           | uu____71964 -> false)
      | FStar_Syntax_Syntax.Tm_quoted uu____71982 -> false
      | FStar_Syntax_Syntax.Tm_meta (t2,uu____71991) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_app (head1,uu____71997) ->
          is_type_aux env head1
  
let (is_type :
  FStar_Extraction_ML_UEnv.uenv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      FStar_Extraction_ML_UEnv.debug env
        (fun uu____72038  ->
           let uu____72039 = FStar_Syntax_Print.tag_of_term t  in
           let uu____72041 = FStar_Syntax_Print.term_to_string t  in
           FStar_Util.print2 "checking is_type (%s) %s\n" uu____72039
             uu____72041);
      (let b = is_type_aux env t  in
       FStar_Extraction_ML_UEnv.debug env
         (fun uu____72050  ->
            if b
            then
              let uu____72052 = FStar_Syntax_Print.term_to_string t  in
              let uu____72054 = FStar_Syntax_Print.tag_of_term t  in
              FStar_Util.print2 "yes, is_type %s (%s)\n" uu____72052
                uu____72054
            else
              (let uu____72059 = FStar_Syntax_Print.term_to_string t  in
               let uu____72061 = FStar_Syntax_Print.tag_of_term t  in
               FStar_Util.print2 "not a type %s (%s)\n" uu____72059
                 uu____72061));
       b)
  
let is_type_binder :
  'Auu____72071 .
    FStar_Extraction_ML_UEnv.uenv ->
      (FStar_Syntax_Syntax.bv * 'Auu____72071) -> Prims.bool
  =
  fun env  ->
    fun x  ->
      is_arity env (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
  
let (is_constructor : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____72098 =
      let uu____72099 = FStar_Syntax_Subst.compress t  in
      uu____72099.FStar_Syntax_Syntax.n  in
    match uu____72098 with
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____72103;
          FStar_Syntax_Syntax.fv_delta = uu____72104;
          FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
            (FStar_Syntax_Syntax.Data_ctor );_}
        -> true
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____72106;
          FStar_Syntax_Syntax.fv_delta = uu____72107;
          FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
            (FStar_Syntax_Syntax.Record_ctor uu____72108);_}
        -> true
    | uu____72116 -> false
  
let rec (is_fstar_value : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____72125 =
      let uu____72126 = FStar_Syntax_Subst.compress t  in
      uu____72126.FStar_Syntax_Syntax.n  in
    match uu____72125 with
    | FStar_Syntax_Syntax.Tm_constant uu____72130 -> true
    | FStar_Syntax_Syntax.Tm_bvar uu____72132 -> true
    | FStar_Syntax_Syntax.Tm_fvar uu____72134 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____72136 -> true
    | FStar_Syntax_Syntax.Tm_app (head1,args) ->
        let uu____72182 = is_constructor head1  in
        if uu____72182
        then
          FStar_All.pipe_right args
            (FStar_List.for_all
               (fun uu____72204  ->
                  match uu____72204 with
                  | (te,uu____72213) -> is_fstar_value te))
        else false
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____72222) -> is_fstar_value t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____72228,uu____72229) ->
        is_fstar_value t1
    | uu____72270 -> false
  
let rec (is_ml_value : FStar_Extraction_ML_Syntax.mlexpr -> Prims.bool) =
  fun e  ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_Const uu____72280 -> true
    | FStar_Extraction_ML_Syntax.MLE_Var uu____72282 -> true
    | FStar_Extraction_ML_Syntax.MLE_Name uu____72285 -> true
    | FStar_Extraction_ML_Syntax.MLE_Fun uu____72287 -> true
    | FStar_Extraction_ML_Syntax.MLE_CTor (uu____72300,exps) ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Tuple exps ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Record (uu____72309,fields) ->
        FStar_Util.for_all
          (fun uu____72339  ->
             match uu____72339 with | (uu____72346,e1) -> is_ml_value e1)
          fields
    | FStar_Extraction_ML_Syntax.MLE_TApp (h,uu____72351) -> is_ml_value h
    | uu____72356 -> false
  
let (fresh : Prims.string -> Prims.string) =
  let c = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun x  ->
    FStar_Util.incr c;
    (let uu____72407 =
       let uu____72409 = FStar_ST.op_Bang c  in
       FStar_Util.string_of_int uu____72409  in
     Prims.op_Hat x uu____72407)
  
let (normalize_abs : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t0  ->
    let rec aux bs t copt =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_abs (bs',body,copt1) ->
          aux (FStar_List.append bs bs') body copt1
      | uu____72534 ->
          let e' = FStar_Syntax_Util.unascribe t1  in
          let uu____72536 = FStar_Syntax_Util.is_fun e'  in
          if uu____72536
          then aux bs e' copt
          else FStar_Syntax_Util.abs bs e' copt
       in
    aux [] t0 FStar_Pervasives_Native.None
  
let (unit_binder : FStar_Syntax_Syntax.binder) =
  let uu____72550 =
    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
      FStar_Syntax_Syntax.t_unit
     in
  FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____72550 
let (check_pats_for_ite :
  (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term
    FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term) Prims.list ->
    (Prims.bool * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option *
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option))
  =
  fun l  ->
    let def =
      (false, FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)  in
    if (FStar_List.length l) <> (Prims.parse_int "2")
    then def
    else
      (let uu____72641 = FStar_List.hd l  in
       match uu____72641 with
       | (p1,w1,e1) ->
           let uu____72676 =
             let uu____72685 = FStar_List.tl l  in FStar_List.hd uu____72685
              in
           (match uu____72676 with
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
                 | uu____72769 -> def)))
  
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
      let uu____72808 = FStar_Extraction_ML_Util.doms_and_cod t  in
      match uu____72808 with
      | (ts,r) ->
          if ts = []
          then e
          else
            (let vs = FStar_List.map (fun uu____72832  -> fresh "a") ts  in
             let vs_ts = FStar_List.zip vs ts  in
             let vs_es =
               let uu____72846 = FStar_List.zip vs ts  in
               FStar_List.map
                 (fun uu____72863  ->
                    match uu____72863 with
                    | (v1,t1) ->
                        FStar_Extraction_ML_Syntax.with_ty t1
                          (FStar_Extraction_ML_Syntax.MLE_Var v1))
                 uu____72846
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
      let uu____72894 = FStar_Extraction_ML_Util.doms_and_cod t  in
      match uu____72894 with
      | (ts,r) ->
          let body r1 =
            let r2 =
              let uu____72914 = FStar_Extraction_ML_Util.udelta_unfold g r1
                 in
              match uu____72914 with
              | FStar_Pervasives_Native.None  -> r1
              | FStar_Pervasives_Native.Some r2 -> r2  in
            match r2 with
            | FStar_Extraction_ML_Syntax.MLTY_Erased  ->
                FStar_Extraction_ML_Syntax.ml_unit
            | FStar_Extraction_ML_Syntax.MLTY_Top  ->
                FStar_Extraction_ML_Syntax.apply_obj_repr
                  FStar_Extraction_ML_Syntax.ml_unit
                  FStar_Extraction_ML_Syntax.MLTY_Erased
            | uu____72918 ->
                FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty r2)
                  (FStar_Extraction_ML_Syntax.MLE_Coerce
                     (FStar_Extraction_ML_Syntax.ml_unit,
                       FStar_Extraction_ML_Syntax.MLTY_Erased, r2))
             in
          if ts = []
          then body r
          else
            (let vs = FStar_List.map (fun uu____72930  -> fresh "a") ts  in
             let vs_ts = FStar_List.zip vs ts  in
             let uu____72941 =
               let uu____72942 =
                 let uu____72954 = body r  in (vs_ts, uu____72954)  in
               FStar_Extraction_ML_Syntax.MLE_Fun uu____72942  in
             FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t)
               uu____72941)
  
let (maybe_eta_expand :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun expect  ->
    fun e  ->
      let uu____72973 =
        (FStar_Options.ml_no_eta_expand_coertions ()) ||
          (let uu____72976 = FStar_Options.codegen ()  in
           uu____72976 = (FStar_Pervasives_Native.Some FStar_Options.Kremlin))
         in
      if uu____72973 then e else eta_expand expect e
  
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
            | uu____73054 ->
                FStar_Extraction_ML_Syntax.MLE_Fun ([binder], body)
             in
          let rec aux e1 ty1 expect1 =
            let coerce_branch uu____73109 =
              match uu____73109 with
              | (pat,w,b) ->
                  let uu____73133 = aux b ty1 expect1  in
                  (pat, w, uu____73133)
               in
            match ((e1.FStar_Extraction_ML_Syntax.expr), ty1, expect1) with
            | (FStar_Extraction_ML_Syntax.MLE_Fun
               (arg::rest,body),FStar_Extraction_ML_Syntax.MLTY_Fun
               (t0,uu____73140,t1),FStar_Extraction_ML_Syntax.MLTY_Fun
               (s0,uu____73143,s1)) ->
                let body1 =
                  match rest with
                  | [] -> body
                  | uu____73175 ->
                      FStar_Extraction_ML_Syntax.with_ty t1
                        (FStar_Extraction_ML_Syntax.MLE_Fun (rest, body))
                   in
                let body2 = aux body1 t1 s1  in
                let uu____73191 = type_leq g s0 t0  in
                if uu____73191
                then
                  FStar_Extraction_ML_Syntax.with_ty expect1
                    (mk_fun arg body2)
                else
                  (let lb =
                     let uu____73197 =
                       let uu____73198 =
                         let uu____73199 =
                           let uu____73206 =
                             FStar_All.pipe_left
                               (FStar_Extraction_ML_Syntax.with_ty s0)
                               (FStar_Extraction_ML_Syntax.MLE_Var
                                  (FStar_Pervasives_Native.fst arg))
                              in
                           (uu____73206, s0, t0)  in
                         FStar_Extraction_ML_Syntax.MLE_Coerce uu____73199
                          in
                       FStar_Extraction_ML_Syntax.with_ty t0 uu____73198  in
                     {
                       FStar_Extraction_ML_Syntax.mllb_name =
                         (FStar_Pervasives_Native.fst arg);
                       FStar_Extraction_ML_Syntax.mllb_tysc =
                         (FStar_Pervasives_Native.Some ([], t0));
                       FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                       FStar_Extraction_ML_Syntax.mllb_def = uu____73197;
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
               (lbs,body),uu____73225,uu____73226) ->
                let uu____73239 =
                  let uu____73240 =
                    let uu____73251 = aux body ty1 expect1  in
                    (lbs, uu____73251)  in
                  FStar_Extraction_ML_Syntax.MLE_Let uu____73240  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____73239
            | (FStar_Extraction_ML_Syntax.MLE_Match
               (s,branches),uu____73260,uu____73261) ->
                let uu____73282 =
                  let uu____73283 =
                    let uu____73298 = FStar_List.map coerce_branch branches
                       in
                    (s, uu____73298)  in
                  FStar_Extraction_ML_Syntax.MLE_Match uu____73283  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____73282
            | (FStar_Extraction_ML_Syntax.MLE_If
               (s,b1,b2_opt),uu____73338,uu____73339) ->
                let uu____73344 =
                  let uu____73345 =
                    let uu____73354 = aux b1 ty1 expect1  in
                    let uu____73355 =
                      FStar_Util.map_opt b2_opt
                        (fun b2  -> aux b2 ty1 expect1)
                       in
                    (s, uu____73354, uu____73355)  in
                  FStar_Extraction_ML_Syntax.MLE_If uu____73345  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____73344
            | (FStar_Extraction_ML_Syntax.MLE_Seq es,uu____73363,uu____73364)
                ->
                let uu____73367 = FStar_Util.prefix es  in
                (match uu____73367 with
                 | (prefix1,last1) ->
                     let uu____73380 =
                       let uu____73381 =
                         let uu____73384 =
                           let uu____73387 = aux last1 ty1 expect1  in
                           [uu____73387]  in
                         FStar_List.append prefix1 uu____73384  in
                       FStar_Extraction_ML_Syntax.MLE_Seq uu____73381  in
                     FStar_All.pipe_left
                       (FStar_Extraction_ML_Syntax.with_ty expect1)
                       uu____73380)
            | (FStar_Extraction_ML_Syntax.MLE_Try
               (s,branches),uu____73390,uu____73391) ->
                let uu____73412 =
                  let uu____73413 =
                    let uu____73428 = FStar_List.map coerce_branch branches
                       in
                    (s, uu____73428)  in
                  FStar_Extraction_ML_Syntax.MLE_Try uu____73413  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____73412
            | uu____73465 ->
                FStar_Extraction_ML_Syntax.with_ty expect1
                  (FStar_Extraction_ML_Syntax.MLE_Coerce (e1, ty1, expect1))
             in
          aux e ty expect
  
let maybe_coerce :
  'Auu____73485 .
    'Auu____73485 ->
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
            let uu____73512 =
              type_leq_c g (FStar_Pervasives_Native.Some e) ty1 expect  in
            match uu____73512 with
            | (true ,FStar_Pervasives_Native.Some e') -> e'
            | uu____73525 ->
                (match ty1 with
                 | FStar_Extraction_ML_Syntax.MLTY_Erased  ->
                     default_value_for_ty g expect
                 | uu____73533 ->
                     let uu____73534 =
                       let uu____73536 =
                         FStar_Extraction_ML_Util.erase_effect_annotations
                           ty1
                          in
                       let uu____73537 =
                         FStar_Extraction_ML_Util.erase_effect_annotations
                           expect
                          in
                       type_leq g uu____73536 uu____73537  in
                     if uu____73534
                     then
                       (FStar_Extraction_ML_UEnv.debug g
                          (fun uu____73543  ->
                             let uu____73544 =
                               FStar_Extraction_ML_Code.string_of_mlexpr
                                 g.FStar_Extraction_ML_UEnv.currentModule e
                                in
                             let uu____73546 =
                               FStar_Extraction_ML_Code.string_of_mlty
                                 g.FStar_Extraction_ML_UEnv.currentModule ty1
                                in
                             FStar_Util.print2
                               "\n Effect mismatch on type of %s : %s\n"
                               uu____73544 uu____73546);
                        e)
                     else
                       (FStar_Extraction_ML_UEnv.debug g
                          (fun uu____73556  ->
                             let uu____73557 =
                               FStar_Extraction_ML_Code.string_of_mlexpr
                                 g.FStar_Extraction_ML_UEnv.currentModule e
                                in
                             let uu____73559 =
                               FStar_Extraction_ML_Code.string_of_mlty
                                 g.FStar_Extraction_ML_UEnv.currentModule ty1
                                in
                             let uu____73561 =
                               FStar_Extraction_ML_Code.string_of_mlty
                                 g.FStar_Extraction_ML_UEnv.currentModule
                                 expect
                                in
                             FStar_Util.print3
                               "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n"
                               uu____73557 uu____73559 uu____73561);
                        (let uu____73564 = apply_coercion g e ty1 expect  in
                         maybe_eta_expand expect uu____73564)))
  
let (bv_as_mlty :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun bv  ->
      let uu____73576 = FStar_Extraction_ML_UEnv.lookup_bv g bv  in
      match uu____73576 with
      | FStar_Util.Inl ty_b -> ty_b.FStar_Extraction_ML_UEnv.ty_b_ty
      | uu____73578 -> FStar_Extraction_ML_Syntax.MLTY_Top
  
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
    | FStar_Syntax_Syntax.Total uu____73596 -> c
    | FStar_Syntax_Syntax.GTotal uu____73605 -> c
    | FStar_Syntax_Syntax.Comp ct ->
        let effect_args =
          FStar_List.map
            (fun uu____73641  ->
               match uu____73641 with
               | (uu____73656,aq) -> (FStar_Syntax_Syntax.t_unit, aq))
            ct.FStar_Syntax_Syntax.effect_args
           in
        let ct1 =
          let uu___1129_73669 = ct  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___1129_73669.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___1129_73669.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ =
              (uu___1129_73669.FStar_Syntax_Syntax.result_typ);
            FStar_Syntax_Syntax.effect_args = effect_args;
            FStar_Syntax_Syntax.flags =
              (uu___1129_73669.FStar_Syntax_Syntax.flags)
          }  in
        let c1 =
          let uu___1132_73673 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
            FStar_Syntax_Syntax.pos =
              (uu___1132_73673.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___1132_73673.FStar_Syntax_Syntax.vars)
          }  in
        c1
  
let rec (translate_term_to_mlty :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun t0  ->
      let arg_as_mlty g1 uu____73722 =
        match uu____73722 with
        | (a,uu____73730) ->
            let uu____73735 = is_type g1 a  in
            if uu____73735
            then translate_term_to_mlty g1 a
            else FStar_Extraction_ML_UEnv.erasedContent
         in
      let fv_app_as_mlty g1 fv args =
        let uu____73756 =
          let uu____73758 = FStar_Extraction_ML_UEnv.is_fv_type g1 fv  in
          Prims.op_Negation uu____73758  in
        if uu____73756
        then FStar_Extraction_ML_Syntax.MLTY_Top
        else
          (let uu____73763 =
             let uu____73778 =
               FStar_TypeChecker_Env.lookup_lid
                 g1.FStar_Extraction_ML_UEnv.env_tcenv
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             match uu____73778 with
             | ((uu____73801,fvty),uu____73803) ->
                 let fvty1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Env.UnfoldUntil
                        FStar_Syntax_Syntax.delta_constant]
                     g1.FStar_Extraction_ML_UEnv.env_tcenv fvty
                    in
                 FStar_Syntax_Util.arrow_formals fvty1
              in
           match uu____73763 with
           | (formals,uu____73810) ->
               let mlargs = FStar_List.map (arg_as_mlty g1) args  in
               let mlargs1 =
                 let n_args = FStar_List.length args  in
                 if (FStar_List.length formals) > n_args
                 then
                   let uu____73867 = FStar_Util.first_N n_args formals  in
                   match uu____73867 with
                   | (uu____73900,rest) ->
                       let uu____73934 =
                         FStar_List.map
                           (fun uu____73944  ->
                              FStar_Extraction_ML_UEnv.erasedContent) rest
                          in
                       FStar_List.append mlargs uu____73934
                 else mlargs  in
               let nm =
                 let uu____73954 =
                   FStar_Extraction_ML_UEnv.maybe_mangle_type_projector g1 fv
                    in
                 match uu____73954 with
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
        | FStar_Syntax_Syntax.Tm_type uu____73972 ->
            FStar_Extraction_ML_Syntax.MLTY_Erased
        | FStar_Syntax_Syntax.Tm_bvar uu____73973 ->
            let uu____73974 =
              let uu____73976 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____73976
               in
            failwith uu____73974
        | FStar_Syntax_Syntax.Tm_delayed uu____73979 ->
            let uu____74002 =
              let uu____74004 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____74004
               in
            failwith uu____74002
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____74007 =
              let uu____74009 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____74009
               in
            failwith uu____74007
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____74013 = FStar_Syntax_Util.unfold_lazy i  in
            translate_term_to_mlty env uu____74013
        | FStar_Syntax_Syntax.Tm_constant uu____74014 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_quoted uu____74015 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_uvar uu____74022 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_meta (t2,uu____74036) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____74041;
               FStar_Syntax_Syntax.index = uu____74042;
               FStar_Syntax_Syntax.sort = t2;_},uu____74044)
            -> translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_uinst (t2,uu____74053) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____74059,uu____74060) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
        | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv []
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let uu____74133 = FStar_Syntax_Subst.open_comp bs c  in
            (match uu____74133 with
             | (bs1,c1) ->
                 let uu____74140 = binders_as_ml_binders env bs1  in
                 (match uu____74140 with
                  | (mlbs,env1) ->
                      let t_ret =
                        let eff =
                          FStar_TypeChecker_Env.norm_eff_name
                            env1.FStar_Extraction_ML_UEnv.env_tcenv
                            (FStar_Syntax_Util.comp_effect_name c1)
                           in
                        let c2 = comp_no_args c1  in
                        let uu____74173 =
                          let uu____74180 =
                            FStar_TypeChecker_Env.effect_decl_opt
                              env1.FStar_Extraction_ML_UEnv.env_tcenv eff
                             in
                          FStar_Util.must uu____74180  in
                        match uu____74173 with
                        | (ed,qualifiers) ->
                            let uu____74201 =
                              FStar_TypeChecker_Env.is_reifiable_effect
                                g.FStar_Extraction_ML_UEnv.env_tcenv
                                ed.FStar_Syntax_Syntax.mname
                               in
                            if uu____74201
                            then
                              let t2 =
                                FStar_TypeChecker_Env.reify_comp
                                  env1.FStar_Extraction_ML_UEnv.env_tcenv c2
                                  FStar_Syntax_Syntax.U_unknown
                                 in
                              (FStar_Extraction_ML_UEnv.debug env1
                                 (fun uu____74209  ->
                                    let uu____74210 =
                                      FStar_Syntax_Print.comp_to_string c2
                                       in
                                    let uu____74212 =
                                      FStar_Syntax_Print.term_to_string t2
                                       in
                                    FStar_Util.print2
                                      "Translating comp type %s as %s\n"
                                      uu____74210 uu____74212);
                               (let res = translate_term_to_mlty env1 t2  in
                                FStar_Extraction_ML_UEnv.debug env1
                                  (fun uu____74221  ->
                                     let uu____74222 =
                                       FStar_Syntax_Print.comp_to_string c2
                                        in
                                     let uu____74224 =
                                       FStar_Syntax_Print.term_to_string t2
                                        in
                                     let uu____74226 =
                                       FStar_Extraction_ML_Code.string_of_mlty
                                         env1.FStar_Extraction_ML_UEnv.currentModule
                                         res
                                        in
                                     FStar_Util.print3
                                       "Translated comp type %s as %s ... to %s\n"
                                       uu____74222 uu____74224 uu____74226);
                                res))
                            else
                              translate_term_to_mlty env1
                                (FStar_Syntax_Util.comp_result c2)
                         in
                      let erase =
                        effect_as_etag env1
                          (FStar_Syntax_Util.comp_effect_name c1)
                         in
                      let uu____74232 =
                        FStar_List.fold_right
                          (fun uu____74252  ->
                             fun uu____74253  ->
                               match (uu____74252, uu____74253) with
                               | ((uu____74276,t2),(tag,t')) ->
                                   (FStar_Extraction_ML_Syntax.E_PURE,
                                     (FStar_Extraction_ML_Syntax.MLTY_Fun
                                        (t2, tag, t')))) mlbs (erase, t_ret)
                         in
                      (match uu____74232 with | (uu____74291,t2) -> t2)))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let res =
              let uu____74320 =
                let uu____74321 = FStar_Syntax_Util.un_uinst head1  in
                uu____74321.FStar_Syntax_Syntax.n  in
              match uu____74320 with
              | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv args
              | FStar_Syntax_Syntax.Tm_app (head2,args') ->
                  let uu____74352 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_app
                         (head2, (FStar_List.append args' args)))
                      FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                     in
                  translate_term_to_mlty env uu____74352
              | uu____74373 -> FStar_Extraction_ML_UEnv.unknownType  in
            res
        | FStar_Syntax_Syntax.Tm_abs (bs,ty,uu____74376) ->
            let uu____74401 = FStar_Syntax_Subst.open_term bs ty  in
            (match uu____74401 with
             | (bs1,ty1) ->
                 let uu____74408 = binders_as_ml_binders env bs1  in
                 (match uu____74408 with
                  | (bts,env1) -> translate_term_to_mlty env1 ty1))
        | FStar_Syntax_Syntax.Tm_let uu____74436 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_match uu____74450 ->
            FStar_Extraction_ML_UEnv.unknownType
         in
      let rec is_top_ty t =
        match t with
        | FStar_Extraction_ML_Syntax.MLTY_Top  -> true
        | FStar_Extraction_ML_Syntax.MLTY_Named uu____74482 ->
            let uu____74489 = FStar_Extraction_ML_Util.udelta_unfold g t  in
            (match uu____74489 with
             | FStar_Pervasives_Native.None  -> false
             | FStar_Pervasives_Native.Some t1 -> is_top_ty t1)
        | uu____74495 -> false  in
      let uu____74497 =
        FStar_TypeChecker_Util.must_erase_for_extraction
          g.FStar_Extraction_ML_UEnv.env_tcenv t0
         in
      if uu____74497
      then FStar_Extraction_ML_Syntax.MLTY_Erased
      else
        (let mlt = aux g t0  in
         let uu____74503 = is_top_ty mlt  in
         if uu____74503
         then
           let t =
             FStar_TypeChecker_Normalize.normalize
               ((FStar_TypeChecker_Env.UnfoldUntil
                   FStar_Syntax_Syntax.delta_constant) :: basic_norm_steps)
               g.FStar_Extraction_ML_UEnv.env_tcenv t0
              in
           aux g t
         else mlt)

and (binders_as_ml_binders :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.binders ->
      ((FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)
        Prims.list * FStar_Extraction_ML_UEnv.uenv))
  =
  fun g  ->
    fun bs  ->
      let uu____74522 =
        FStar_All.pipe_right bs
          (FStar_List.fold_left
             (fun uu____74578  ->
                fun b  ->
                  match uu____74578 with
                  | (ml_bs,env) ->
                      let uu____74624 = is_type_binder g b  in
                      if uu____74624
                      then
                        let b1 = FStar_Pervasives_Native.fst b  in
                        let env1 =
                          FStar_Extraction_ML_UEnv.extend_ty env b1
                            (FStar_Pervasives_Native.Some
                               FStar_Extraction_ML_Syntax.MLTY_Top)
                           in
                        let ml_b =
                          let uu____74650 =
                            FStar_Extraction_ML_UEnv.bv_as_ml_termvar b1  in
                          (uu____74650,
                            FStar_Extraction_ML_Syntax.ml_unit_ty)
                           in
                        ((ml_b :: ml_bs), env1)
                      else
                        (let b1 = FStar_Pervasives_Native.fst b  in
                         let t =
                           translate_term_to_mlty env
                             b1.FStar_Syntax_Syntax.sort
                            in
                         let uu____74671 =
                           FStar_Extraction_ML_UEnv.extend_bv env b1 
                             ([], t) false false false
                            in
                         match uu____74671 with
                         | (env1,b2,uu____74696) ->
                             let ml_b =
                               let uu____74705 =
                                 FStar_Extraction_ML_UEnv.removeTick b2  in
                               (uu____74705, t)  in
                             ((ml_b :: ml_bs), env1))) ([], g))
         in
      match uu____74522 with | (ml_bs,env) -> ((FStar_List.rev ml_bs), env)

let (term_as_mlty :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun t0  ->
      let t =
        FStar_TypeChecker_Normalize.normalize basic_norm_steps
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
      | (FStar_Extraction_ML_Syntax.MLE_Seq es1,uu____74801) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (FStar_List.append es1 [e2])
      | (uu____74804,FStar_Extraction_ML_Syntax.MLE_Seq es2) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (e1 :: es2)
      | uu____74808 -> FStar_Extraction_ML_Syntax.MLE_Seq [e1; e2]
  
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
                    | uu____74842 when
                        (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
                          =
                          FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr
                        -> body.FStar_Extraction_ML_Syntax.expr
                    | uu____74843 ->
                        mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def
                          body)
             | uu____74844 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body))
        | uu____74853 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body)
  
let (resugar_pat :
  FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option ->
    FStar_Extraction_ML_Syntax.mlpattern ->
      FStar_Extraction_ML_Syntax.mlpattern)
  =
  fun q  ->
    fun p  ->
      match p with
      | FStar_Extraction_ML_Syntax.MLP_CTor (d,pats) ->
          let uu____74881 = FStar_Extraction_ML_Util.is_xtuple d  in
          (match uu____74881 with
           | FStar_Pervasives_Native.Some n1 ->
               FStar_Extraction_ML_Syntax.MLP_Tuple pats
           | uu____74888 ->
               (match q with
                | FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Record_ctor (ty,fns)) ->
                    let path =
                      FStar_List.map FStar_Ident.text_of_id ty.FStar_Ident.ns
                       in
                    let fs = record_fields fns pats  in
                    FStar_Extraction_ML_Syntax.MLP_Record (path, fs)
                | uu____74921 -> p))
      | uu____74924 -> p
  
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
                       (fun uu____75026  ->
                          let uu____75027 =
                            FStar_Extraction_ML_Code.string_of_mlty
                              g.FStar_Extraction_ML_UEnv.currentModule t'
                             in
                          let uu____75029 =
                            FStar_Extraction_ML_Code.string_of_mlty
                              g.FStar_Extraction_ML_UEnv.currentModule t
                             in
                          FStar_Util.print2
                            "Expected pattern type %s; got pattern type %s\n"
                            uu____75027 uu____75029)
                   else ();
                   ok)
               in
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int
                (c,swopt)) when
                let uu____75065 = FStar_Options.codegen ()  in
                uu____75065 <>
                  (FStar_Pervasives_Native.Some FStar_Options.Kremlin)
                ->
                let uu____75070 =
                  match swopt with
                  | FStar_Pervasives_Native.None  ->
                      let uu____75083 =
                        let uu____75084 =
                          let uu____75085 =
                            FStar_Extraction_ML_Util.mlconst_of_const
                              p.FStar_Syntax_Syntax.p
                              (FStar_Const.Const_int
                                 (c, FStar_Pervasives_Native.None))
                             in
                          FStar_Extraction_ML_Syntax.MLE_Const uu____75085
                           in
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.ml_int_ty)
                          uu____75084
                         in
                      (uu____75083, FStar_Extraction_ML_Syntax.ml_int_ty)
                  | FStar_Pervasives_Native.Some sw ->
                      let source_term =
                        FStar_ToSyntax_ToSyntax.desugar_machine_integer
                          (g.FStar_Extraction_ML_UEnv.env_tcenv).FStar_TypeChecker_Env.dsenv
                          c sw FStar_Range.dummyRange
                         in
                      let uu____75107 = term_as_mlexpr g source_term  in
                      (match uu____75107 with
                       | (mlterm,uu____75119,mlty) -> (mlterm, mlty))
                   in
                (match uu____75070 with
                 | (mlc,ml_ty) ->
                     let x = FStar_Extraction_ML_Syntax.gensym ()  in
                     let when_clause =
                       let uu____75141 =
                         let uu____75142 =
                           let uu____75149 =
                             let uu____75152 =
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty ml_ty)
                                 (FStar_Extraction_ML_Syntax.MLE_Var x)
                                in
                             [uu____75152; mlc]  in
                           (FStar_Extraction_ML_Util.prims_op_equality,
                             uu____75149)
                            in
                         FStar_Extraction_ML_Syntax.MLE_App uu____75142  in
                       FStar_All.pipe_left
                         (FStar_Extraction_ML_Syntax.with_ty
                            FStar_Extraction_ML_Syntax.ml_bool_ty)
                         uu____75141
                        in
                     let uu____75155 = ok ml_ty  in
                     (g,
                       (FStar_Pervasives_Native.Some
                          ((FStar_Extraction_ML_Syntax.MLP_Var x),
                            [when_clause])), uu____75155))
            | FStar_Syntax_Syntax.Pat_constant s ->
                let t =
                  FStar_TypeChecker_TcTerm.tc_constant
                    g.FStar_Extraction_ML_UEnv.env_tcenv
                    FStar_Range.dummyRange s
                   in
                let mlty = term_as_mlty g t  in
                let uu____75177 =
                  let uu____75186 =
                    let uu____75193 =
                      let uu____75194 =
                        FStar_Extraction_ML_Util.mlconst_of_const
                          p.FStar_Syntax_Syntax.p s
                         in
                      FStar_Extraction_ML_Syntax.MLP_Const uu____75194  in
                    (uu____75193, [])  in
                  FStar_Pervasives_Native.Some uu____75186  in
                let uu____75203 = ok mlty  in (g, uu____75177, uu____75203)
            | FStar_Syntax_Syntax.Pat_var x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort  in
                let uu____75216 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp
                   in
                (match uu____75216 with
                 | (g1,x1,uu____75244) ->
                     let uu____75247 = ok mlty  in
                     (g1,
                       (if imp
                        then FStar_Pervasives_Native.None
                        else
                          FStar_Pervasives_Native.Some
                            ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                       uu____75247))
            | FStar_Syntax_Syntax.Pat_wild x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort  in
                let uu____75285 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp
                   in
                (match uu____75285 with
                 | (g1,x1,uu____75313) ->
                     let uu____75316 = ok mlty  in
                     (g1,
                       (if imp
                        then FStar_Pervasives_Native.None
                        else
                          FStar_Pervasives_Native.Some
                            ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                       uu____75316))
            | FStar_Syntax_Syntax.Pat_dot_term uu____75352 ->
                (g, FStar_Pervasives_Native.None, true)
            | FStar_Syntax_Syntax.Pat_cons (f,pats) ->
                let uu____75395 =
                  let uu____75404 = FStar_Extraction_ML_UEnv.lookup_fv g f
                     in
                  match uu____75404 with
                  | { FStar_Extraction_ML_UEnv.exp_b_name = uu____75413;
                      FStar_Extraction_ML_UEnv.exp_b_expr =
                        {
                          FStar_Extraction_ML_Syntax.expr =
                            FStar_Extraction_ML_Syntax.MLE_Name n1;
                          FStar_Extraction_ML_Syntax.mlty = uu____75415;
                          FStar_Extraction_ML_Syntax.loc = uu____75416;_};
                      FStar_Extraction_ML_UEnv.exp_b_tscheme = ttys;
                      FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____75418;_}
                      -> (n1, ttys)
                  | uu____75425 -> failwith "Expected a constructor"  in
                (match uu____75395 with
                 | (d,tys) ->
                     let nTyVars =
                       FStar_List.length (FStar_Pervasives_Native.fst tys)
                        in
                     let uu____75462 = FStar_Util.first_N nTyVars pats  in
                     (match uu____75462 with
                      | (tysVarPats,restPats) ->
                          let f_ty_opt =
                            try
                              (fun uu___1428_75570  ->
                                 match () with
                                 | () ->
                                     let mlty_args =
                                       FStar_All.pipe_right tysVarPats
                                         (FStar_List.map
                                            (fun uu____75601  ->
                                               match uu____75601 with
                                               | (p1,uu____75608) ->
                                                   (match p1.FStar_Syntax_Syntax.v
                                                    with
                                                    | FStar_Syntax_Syntax.Pat_dot_term
                                                        (uu____75611,t) ->
                                                        term_as_mlty g t
                                                    | uu____75617 ->
                                                        (FStar_Extraction_ML_UEnv.debug
                                                           g
                                                           (fun uu____75621 
                                                              ->
                                                              let uu____75622
                                                                =
                                                                FStar_Syntax_Print.pat_to_string
                                                                  p1
                                                                 in
                                                              FStar_Util.print1
                                                                "Pattern %s is not extractable"
                                                                uu____75622);
                                                         FStar_Exn.raise
                                                           Un_extractable))))
                                        in
                                     let f_ty =
                                       FStar_Extraction_ML_Util.subst tys
                                         mlty_args
                                        in
                                     let uu____75626 =
                                       FStar_Extraction_ML_Util.uncurry_mlty_fun
                                         f_ty
                                        in
                                     FStar_Pervasives_Native.Some uu____75626)
                                ()
                            with
                            | Un_extractable  -> FStar_Pervasives_Native.None
                             in
                          let uu____75655 =
                            FStar_Util.fold_map
                              (fun g1  ->
                                 fun uu____75692  ->
                                   match uu____75692 with
                                   | (p1,imp1) ->
                                       let uu____75714 =
                                         extract_one_pat true g1 p1
                                           FStar_Pervasives_Native.None
                                           term_as_mlexpr
                                          in
                                       (match uu____75714 with
                                        | (g2,p2,uu____75745) -> (g2, p2))) g
                              tysVarPats
                             in
                          (match uu____75655 with
                           | (g1,tyMLPats) ->
                               let uu____75809 =
                                 FStar_Util.fold_map
                                   (fun uu____75874  ->
                                      fun uu____75875  ->
                                        match (uu____75874, uu____75875) with
                                        | ((g2,f_ty_opt1),(p1,imp1)) ->
                                            let uu____75973 =
                                              match f_ty_opt1 with
                                              | FStar_Pervasives_Native.Some
                                                  (hd1::rest,res) ->
                                                  ((FStar_Pervasives_Native.Some
                                                      (rest, res)),
                                                    (FStar_Pervasives_Native.Some
                                                       hd1))
                                              | uu____76033 ->
                                                  (FStar_Pervasives_Native.None,
                                                    FStar_Pervasives_Native.None)
                                               in
                                            (match uu____75973 with
                                             | (f_ty_opt2,expected_ty) ->
                                                 let uu____76104 =
                                                   extract_one_pat false g2
                                                     p1 expected_ty
                                                     term_as_mlexpr
                                                    in
                                                 (match uu____76104 with
                                                  | (g3,p2,uu____76147) ->
                                                      ((g3, f_ty_opt2), p2))))
                                   (g1, f_ty_opt) restPats
                                  in
                               (match uu____75809 with
                                | ((g2,f_ty_opt1),restMLPats) ->
                                    let uu____76268 =
                                      let uu____76279 =
                                        FStar_All.pipe_right
                                          (FStar_List.append tyMLPats
                                             restMLPats)
                                          (FStar_List.collect
                                             (fun uu___618_76330  ->
                                                match uu___618_76330 with
                                                | FStar_Pervasives_Native.Some
                                                    x -> [x]
                                                | uu____76372 -> []))
                                         in
                                      FStar_All.pipe_right uu____76279
                                        FStar_List.split
                                       in
                                    (match uu____76268 with
                                     | (mlPats,when_clauses) ->
                                         let pat_ty_compat =
                                           match f_ty_opt1 with
                                           | FStar_Pervasives_Native.Some
                                               ([],t) -> ok t
                                           | uu____76448 -> false  in
                                         let uu____76458 =
                                           let uu____76467 =
                                             let uu____76474 =
                                               resugar_pat
                                                 f.FStar_Syntax_Syntax.fv_qual
                                                 (FStar_Extraction_ML_Syntax.MLP_CTor
                                                    (d, mlPats))
                                                in
                                             let uu____76477 =
                                               FStar_All.pipe_right
                                                 when_clauses
                                                 FStar_List.flatten
                                                in
                                             (uu____76474, uu____76477)  in
                                           FStar_Pervasives_Native.Some
                                             uu____76467
                                            in
                                         (g2, uu____76458, pat_ty_compat))))))
  
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
            let uu____76609 =
              extract_one_pat false g1 p1 expected_t1 term_as_mlexpr  in
            match uu____76609 with
            | (g2,FStar_Pervasives_Native.Some (x,v1),b) -> (g2, (x, v1), b)
            | uu____76672 ->
                failwith "Impossible: Unable to translate pattern"
             in
          let mk_when_clause whens =
            match whens with
            | [] -> FStar_Pervasives_Native.None
            | hd1::tl1 ->
                let uu____76720 =
                  FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd1
                    tl1
                   in
                FStar_Pervasives_Native.Some uu____76720
             in
          let uu____76721 =
            extract_one_pat1 g p (FStar_Pervasives_Native.Some expected_t)
             in
          match uu____76721 with
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
            | FStar_Extraction_ML_Syntax.MLTY_Fun (t0,uu____76881,t1) ->
                let x = FStar_Extraction_ML_Syntax.gensym ()  in
                let uu____76885 =
                  let uu____76897 =
                    let uu____76907 =
                      FStar_All.pipe_left
                        (FStar_Extraction_ML_Syntax.with_ty t0)
                        (FStar_Extraction_ML_Syntax.MLE_Var x)
                       in
                    ((x, t0), uu____76907)  in
                  uu____76897 :: more_args  in
                eta_args uu____76885 t1
            | FStar_Extraction_ML_Syntax.MLTY_Named (uu____76923,uu____76924)
                -> ((FStar_List.rev more_args), t)
            | uu____76949 ->
                let uu____76950 =
                  let uu____76952 =
                    FStar_Extraction_ML_Code.string_of_mlexpr
                      g.FStar_Extraction_ML_UEnv.currentModule mlAppExpr
                     in
                  let uu____76954 =
                    FStar_Extraction_ML_Code.string_of_mlty
                      g.FStar_Extraction_ML_UEnv.currentModule t
                     in
                  FStar_Util.format2
                    "Impossible: Head type is not an arrow: (%s : %s)"
                    uu____76952 uu____76954
                   in
                failwith uu____76950
             in
          let as_record qual1 e =
            match ((e.FStar_Extraction_ML_Syntax.expr), qual1) with
            | (FStar_Extraction_ML_Syntax.MLE_CTor
               (uu____76989,args),FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Record_ctor (tyname,fields))) ->
                let path =
                  FStar_List.map FStar_Ident.text_of_id tyname.FStar_Ident.ns
                   in
                let fields1 = record_fields fields args  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     e.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_Record (path, fields1))
            | uu____77026 -> e  in
          let resugar_and_maybe_eta qual1 e =
            let uu____77048 = eta_args [] residualType  in
            match uu____77048 with
            | (eargs,tres) ->
                (match eargs with
                 | [] ->
                     let uu____77106 = as_record qual1 e  in
                     FStar_Extraction_ML_Util.resugar_exp uu____77106
                 | uu____77107 ->
                     let uu____77119 = FStar_List.unzip eargs  in
                     (match uu____77119 with
                      | (binders,eargs1) ->
                          (match e.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_CTor (head1,args)
                               ->
                               let body =
                                 let uu____77165 =
                                   let uu____77166 =
                                     FStar_All.pipe_left
                                       (FStar_Extraction_ML_Syntax.with_ty
                                          tres)
                                       (FStar_Extraction_ML_Syntax.MLE_CTor
                                          (head1,
                                            (FStar_List.append args eargs1)))
                                      in
                                   FStar_All.pipe_left (as_record qual1)
                                     uu____77166
                                    in
                                 FStar_All.pipe_left
                                   FStar_Extraction_ML_Util.resugar_exp
                                   uu____77165
                                  in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    e.FStar_Extraction_ML_Syntax.mlty)
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    (binders, body))
                           | uu____77176 ->
                               failwith "Impossible: Not a constructor")))
             in
          match ((mlAppExpr.FStar_Extraction_ML_Syntax.expr), qual) with
          | (uu____77180,FStar_Pervasives_Native.None ) -> mlAppExpr
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____77184;
                FStar_Extraction_ML_Syntax.loc = uu____77185;_},mle::args),FStar_Pervasives_Native.Some
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
                | uu____77208 ->
                    let uu____77211 =
                      let uu____77218 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj
                         in
                      (uu____77218, args)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____77211
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
                     FStar_Extraction_ML_Syntax.mlty = uu____77222;
                     FStar_Extraction_ML_Syntax.loc = uu____77223;_},uu____77224);
                FStar_Extraction_ML_Syntax.mlty = uu____77225;
                FStar_Extraction_ML_Syntax.loc = uu____77226;_},mle::args),FStar_Pervasives_Native.Some
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
                | uu____77253 ->
                    let uu____77256 =
                      let uu____77263 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj
                         in
                      (uu____77263, args)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____77256
                 in
              FStar_Extraction_ML_Syntax.with_ty
                mlAppExpr.FStar_Extraction_ML_Syntax.mlty e
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____77267;
                FStar_Extraction_ML_Syntax.loc = uu____77268;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____77276 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____77276
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____77280;
                FStar_Extraction_ML_Syntax.loc = uu____77281;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____77283)) ->
              let uu____77296 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____77296
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____77300;
                     FStar_Extraction_ML_Syntax.loc = uu____77301;_},uu____77302);
                FStar_Extraction_ML_Syntax.mlty = uu____77303;
                FStar_Extraction_ML_Syntax.loc = uu____77304;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____77316 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____77316
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____77320;
                     FStar_Extraction_ML_Syntax.loc = uu____77321;_},uu____77322);
                FStar_Extraction_ML_Syntax.mlty = uu____77323;
                FStar_Extraction_ML_Syntax.loc = uu____77324;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____77326)) ->
              let uu____77343 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____77343
          | (FStar_Extraction_ML_Syntax.MLE_Name
             mlp,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor
             )) ->
              let uu____77349 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____77349
          | (FStar_Extraction_ML_Syntax.MLE_Name
             mlp,FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____77353)) ->
              let uu____77362 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____77362
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____77366;
                FStar_Extraction_ML_Syntax.loc = uu____77367;_},uu____77368),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____77375 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____77375
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____77379;
                FStar_Extraction_ML_Syntax.loc = uu____77380;_},uu____77381),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____77382)) ->
              let uu____77395 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____77395
          | uu____77398 -> mlAppExpr
  
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
        | uu____77429 -> (ml_e, tag)
  
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
      let maybe_generalize uu____77490 =
        match uu____77490 with
        | { FStar_Syntax_Syntax.lbname = lbname_;
            FStar_Syntax_Syntax.lbunivs = uu____77511;
            FStar_Syntax_Syntax.lbtyp = lbtyp;
            FStar_Syntax_Syntax.lbeff = lbeff;
            FStar_Syntax_Syntax.lbdef = lbdef;
            FStar_Syntax_Syntax.lbattrs = uu____77515;
            FStar_Syntax_Syntax.lbpos = uu____77516;_} ->
            let f_e = effect_as_etag g lbeff  in
            let lbtyp1 = FStar_Syntax_Subst.compress lbtyp  in
            let no_gen uu____77597 =
              let expected_t = term_as_mlty g lbtyp1  in
              (lbname_, f_e, (lbtyp1, ([], ([], expected_t))), false, lbdef)
               in
            let uu____77674 =
              FStar_TypeChecker_Util.must_erase_for_extraction
                g.FStar_Extraction_ML_UEnv.env_tcenv lbtyp1
               in
            if uu____77674
            then
              (lbname_, f_e,
                (lbtyp1, ([], ([], FStar_Extraction_ML_Syntax.MLTY_Erased))),
                false, lbdef)
            else
              (match lbtyp1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                   let uu____77760 = FStar_List.hd bs  in
                   FStar_All.pipe_right uu____77760 (is_type_binder g) ->
                   let uu____77782 = FStar_Syntax_Subst.open_comp bs c  in
                   (match uu____77782 with
                    | (bs1,c1) ->
                        let uu____77808 =
                          let uu____77821 =
                            FStar_Util.prefix_until
                              (fun x  ->
                                 let uu____77867 = is_type_binder g x  in
                                 Prims.op_Negation uu____77867) bs1
                             in
                          match uu____77821 with
                          | FStar_Pervasives_Native.None  ->
                              (bs1, (FStar_Syntax_Util.comp_result c1))
                          | FStar_Pervasives_Native.Some (bs2,b,rest) ->
                              let uu____77994 =
                                FStar_Syntax_Util.arrow (b :: rest) c1  in
                              (bs2, uu____77994)
                           in
                        (match uu____77808 with
                         | (tbinders,tbody) ->
                             let n_tbinders = FStar_List.length tbinders  in
                             let lbdef1 =
                               let uu____78056 = normalize_abs lbdef  in
                               FStar_All.pipe_right uu____78056
                                 FStar_Syntax_Util.unmeta
                                in
                             (match lbdef1.FStar_Syntax_Syntax.n with
                              | FStar_Syntax_Syntax.Tm_abs (bs2,body,copt) ->
                                  let uu____78105 =
                                    FStar_Syntax_Subst.open_term bs2 body  in
                                  (match uu____78105 with
                                   | (bs3,body1) ->
                                       if
                                         n_tbinders <=
                                           (FStar_List.length bs3)
                                       then
                                         let uu____78163 =
                                           FStar_Util.first_N n_tbinders bs3
                                            in
                                         (match uu____78163 with
                                          | (targs,rest_args) ->
                                              let expected_source_ty =
                                                let s =
                                                  FStar_List.map2
                                                    (fun uu____78270  ->
                                                       fun uu____78271  ->
                                                         match (uu____78270,
                                                                 uu____78271)
                                                         with
                                                         | ((x,uu____78297),
                                                            (y,uu____78299))
                                                             ->
                                                             let uu____78320
                                                               =
                                                               let uu____78327
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   y
                                                                  in
                                                               (x,
                                                                 uu____78327)
                                                                in
                                                             FStar_Syntax_Syntax.NT
                                                               uu____78320)
                                                    tbinders targs
                                                   in
                                                FStar_Syntax_Subst.subst s
                                                  tbody
                                                 in
                                              let env =
                                                FStar_List.fold_left
                                                  (fun env  ->
                                                     fun uu____78344  ->
                                                       match uu____78344 with
                                                       | (a,uu____78352) ->
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
                                                let uu____78363 =
                                                  FStar_All.pipe_right targs
                                                    (FStar_List.map
                                                       (fun uu____78382  ->
                                                          match uu____78382
                                                          with
                                                          | (x,uu____78391)
                                                              ->
                                                              FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                                x))
                                                   in
                                                (uu____78363, expected_t)  in
                                              let add_unit =
                                                match rest_args with
                                                | [] ->
                                                    (let uu____78407 =
                                                       is_fstar_value body1
                                                        in
                                                     Prims.op_Negation
                                                       uu____78407)
                                                      ||
                                                      (let uu____78410 =
                                                         FStar_Syntax_Util.is_pure_comp
                                                           c1
                                                          in
                                                       Prims.op_Negation
                                                         uu____78410)
                                                | uu____78412 -> false  in
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
                              | FStar_Syntax_Syntax.Tm_uinst uu____78474 ->
                                  let env =
                                    FStar_List.fold_left
                                      (fun env  ->
                                         fun uu____78493  ->
                                           match uu____78493 with
                                           | (a,uu____78501) ->
                                               FStar_Extraction_ML_UEnv.extend_ty
                                                 env a
                                                 FStar_Pervasives_Native.None)
                                      g tbinders
                                     in
                                  let expected_t = term_as_mlty env tbody  in
                                  let polytype =
                                    let uu____78512 =
                                      FStar_All.pipe_right tbinders
                                        (FStar_List.map
                                           (fun uu____78531  ->
                                              match uu____78531 with
                                              | (x,uu____78540) ->
                                                  FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                    x))
                                       in
                                    (uu____78512, expected_t)  in
                                  let args =
                                    FStar_All.pipe_right tbinders
                                      (FStar_List.map
                                         (fun uu____78584  ->
                                            match uu____78584 with
                                            | (bv,uu____78592) ->
                                                let uu____78597 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    bv
                                                   in
                                                FStar_All.pipe_right
                                                  uu____78597
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
                              | FStar_Syntax_Syntax.Tm_fvar uu____78627 ->
                                  let env =
                                    FStar_List.fold_left
                                      (fun env  ->
                                         fun uu____78640  ->
                                           match uu____78640 with
                                           | (a,uu____78648) ->
                                               FStar_Extraction_ML_UEnv.extend_ty
                                                 env a
                                                 FStar_Pervasives_Native.None)
                                      g tbinders
                                     in
                                  let expected_t = term_as_mlty env tbody  in
                                  let polytype =
                                    let uu____78659 =
                                      FStar_All.pipe_right tbinders
                                        (FStar_List.map
                                           (fun uu____78678  ->
                                              match uu____78678 with
                                              | (x,uu____78687) ->
                                                  FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                    x))
                                       in
                                    (uu____78659, expected_t)  in
                                  let args =
                                    FStar_All.pipe_right tbinders
                                      (FStar_List.map
                                         (fun uu____78731  ->
                                            match uu____78731 with
                                            | (bv,uu____78739) ->
                                                let uu____78744 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    bv
                                                   in
                                                FStar_All.pipe_right
                                                  uu____78744
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
                              | FStar_Syntax_Syntax.Tm_name uu____78774 ->
                                  let env =
                                    FStar_List.fold_left
                                      (fun env  ->
                                         fun uu____78787  ->
                                           match uu____78787 with
                                           | (a,uu____78795) ->
                                               FStar_Extraction_ML_UEnv.extend_ty
                                                 env a
                                                 FStar_Pervasives_Native.None)
                                      g tbinders
                                     in
                                  let expected_t = term_as_mlty env tbody  in
                                  let polytype =
                                    let uu____78806 =
                                      FStar_All.pipe_right tbinders
                                        (FStar_List.map
                                           (fun uu____78825  ->
                                              match uu____78825 with
                                              | (x,uu____78834) ->
                                                  FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                    x))
                                       in
                                    (uu____78806, expected_t)  in
                                  let args =
                                    FStar_All.pipe_right tbinders
                                      (FStar_List.map
                                         (fun uu____78878  ->
                                            match uu____78878 with
                                            | (bv,uu____78886) ->
                                                let uu____78891 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    bv
                                                   in
                                                FStar_All.pipe_right
                                                  uu____78891
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
                              | uu____78921 -> err_value_restriction lbdef1)))
               | uu____78941 -> no_gen ())
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
           fun uu____79092  ->
             match uu____79092 with
             | (lbname,e_tag,(typ,(binders,mltyscheme)),add_unit,_body) ->
                 let uu____79153 =
                   FStar_Extraction_ML_UEnv.extend_lb env lbname typ
                     mltyscheme add_unit is_rec
                    in
                 (match uu____79153 with
                  | (env1,uu____79170,exp_binding) ->
                      let uu____79174 =
                        let uu____79179 = FStar_Util.right lbname  in
                        (uu____79179, exp_binding)  in
                      (env1, uu____79174))) g lbs1
  
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
            (fun uu____79245  ->
               let uu____79246 = FStar_Syntax_Print.term_to_string e  in
               let uu____79248 =
                 FStar_Extraction_ML_Code.string_of_mlty
                   g.FStar_Extraction_ML_UEnv.currentModule ty
                  in
               FStar_Util.print2 "Checking %s at type %s\n" uu____79246
                 uu____79248);
          (match (f, ty) with
           | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____79255) ->
               (FStar_Extraction_ML_Syntax.ml_unit,
                 FStar_Extraction_ML_Syntax.MLTY_Erased)
           | (FStar_Extraction_ML_Syntax.E_PURE
              ,FStar_Extraction_ML_Syntax.MLTY_Erased ) ->
               (FStar_Extraction_ML_Syntax.ml_unit,
                 FStar_Extraction_ML_Syntax.MLTY_Erased)
           | uu____79256 ->
               let uu____79261 = term_as_mlexpr g e  in
               (match uu____79261 with
                | (ml_e,tag,t) ->
                    let uu____79275 = maybe_promote_effect ml_e tag t  in
                    (match uu____79275 with
                     | (ml_e1,tag1) ->
                         let uu____79286 =
                           FStar_Extraction_ML_Util.eff_leq tag1 f  in
                         if uu____79286
                         then
                           let uu____79293 =
                             maybe_coerce e.FStar_Syntax_Syntax.pos g ml_e1 t
                               ty
                              in
                           (uu____79293, ty)
                         else
                           (match (tag1, f, ty) with
                            | (FStar_Extraction_ML_Syntax.E_GHOST
                               ,FStar_Extraction_ML_Syntax.E_PURE
                               ,FStar_Extraction_ML_Syntax.MLTY_Erased ) ->
                                let uu____79300 =
                                  maybe_coerce e.FStar_Syntax_Syntax.pos g
                                    ml_e1 t ty
                                   in
                                (uu____79300, ty)
                            | uu____79301 ->
                                (err_unexpected_eff g e ty f tag1;
                                 (let uu____79309 =
                                    maybe_coerce e.FStar_Syntax_Syntax.pos g
                                      ml_e1 t ty
                                     in
                                  (uu____79309, ty)))))))

and (term_as_mlexpr :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag *
        FStar_Extraction_ML_Syntax.mlty))
  =
  fun g  ->
    fun e  ->
      let uu____79312 = term_as_mlexpr' g e  in
      match uu____79312 with
      | (e1,f,t) ->
          let uu____79328 = maybe_promote_effect e1 f t  in
          (match uu____79328 with | (e2,f1) -> (e2, f1, t))

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
           let uu____79353 =
             let uu____79355 =
               FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos  in
             let uu____79357 = FStar_Syntax_Print.tag_of_term top  in
             let uu____79359 = FStar_Syntax_Print.term_to_string top  in
             FStar_Util.format3 "%s: term_as_mlexpr' (%s) :  %s \n"
               uu____79355 uu____79357 uu____79359
              in
           FStar_Util.print_string uu____79353);
      (let t = FStar_Syntax_Subst.compress top  in
       match t.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____79369 =
             let uu____79371 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____79371
              in
           failwith uu____79369
       | FStar_Syntax_Syntax.Tm_delayed uu____79380 ->
           let uu____79403 =
             let uu____79405 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____79405
              in
           failwith uu____79403
       | FStar_Syntax_Syntax.Tm_uvar uu____79414 ->
           let uu____79427 =
             let uu____79429 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____79429
              in
           failwith uu____79427
       | FStar_Syntax_Syntax.Tm_bvar uu____79438 ->
           let uu____79439 =
             let uu____79441 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____79441
              in
           failwith uu____79439
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____79451 = FStar_Syntax_Util.unfold_lazy i  in
           term_as_mlexpr g uu____79451
       | FStar_Syntax_Syntax.Tm_type uu____79452 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_refine uu____79453 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_arrow uu____79460 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_quoted
           (qt,{
                 FStar_Syntax_Syntax.qkind =
                   FStar_Syntax_Syntax.Quote_dynamic ;
                 FStar_Syntax_Syntax.antiquotes = uu____79476;_})
           ->
           let uu____79489 =
             let uu____79490 =
               FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.failwith_lid
                 FStar_Syntax_Syntax.delta_constant
                 FStar_Pervasives_Native.None
                in
             FStar_Extraction_ML_UEnv.lookup_fv g uu____79490  in
           (match uu____79489 with
            | { FStar_Extraction_ML_UEnv.exp_b_name = uu____79497;
                FStar_Extraction_ML_UEnv.exp_b_expr = fw;
                FStar_Extraction_ML_UEnv.exp_b_tscheme = uu____79499;
                FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____79500;_} ->
                let uu____79503 =
                  let uu____79504 =
                    let uu____79505 =
                      let uu____79512 =
                        let uu____79515 =
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty
                               FStar_Extraction_ML_Syntax.ml_string_ty)
                            (FStar_Extraction_ML_Syntax.MLE_Const
                               (FStar_Extraction_ML_Syntax.MLC_String
                                  "Cannot evaluate open quotation at runtime"))
                           in
                        [uu____79515]  in
                      (fw, uu____79512)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____79505  in
                  FStar_All.pipe_left
                    (FStar_Extraction_ML_Syntax.with_ty
                       FStar_Extraction_ML_Syntax.ml_int_ty) uu____79504
                   in
                (uu____79503, FStar_Extraction_ML_Syntax.E_PURE,
                  FStar_Extraction_ML_Syntax.ml_int_ty))
       | FStar_Syntax_Syntax.Tm_quoted
           (qt,{
                 FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static ;
                 FStar_Syntax_Syntax.antiquotes = aqs;_})
           ->
           let uu____79533 = FStar_Reflection_Basic.inspect_ln qt  in
           (match uu____79533 with
            | FStar_Reflection_Data.Tv_Var bv ->
                let uu____79541 = FStar_Syntax_Syntax.lookup_aq bv aqs  in
                (match uu____79541 with
                 | FStar_Pervasives_Native.Some tm -> term_as_mlexpr g tm
                 | FStar_Pervasives_Native.None  ->
                     let tv =
                       let uu____79552 =
                         let uu____79559 =
                           FStar_Reflection_Embeddings.e_term_view_aq aqs  in
                         FStar_Syntax_Embeddings.embed uu____79559
                           (FStar_Reflection_Data.Tv_Var bv)
                          in
                       uu____79552 t.FStar_Syntax_Syntax.pos
                         FStar_Pervasives_Native.None
                         FStar_Syntax_Embeddings.id_norm_cb
                        in
                     let t1 =
                       let uu____79590 =
                         let uu____79601 = FStar_Syntax_Syntax.as_arg tv  in
                         [uu____79601]  in
                       FStar_Syntax_Util.mk_app
                         (FStar_Reflection_Data.refl_constant_term
                            FStar_Reflection_Data.fstar_refl_pack_ln)
                         uu____79590
                        in
                     term_as_mlexpr g t1)
            | tv ->
                let tv1 =
                  let uu____79628 =
                    let uu____79635 =
                      FStar_Reflection_Embeddings.e_term_view_aq aqs  in
                    FStar_Syntax_Embeddings.embed uu____79635 tv  in
                  uu____79628 t.FStar_Syntax_Syntax.pos
                    FStar_Pervasives_Native.None
                    FStar_Syntax_Embeddings.id_norm_cb
                   in
                let t1 =
                  let uu____79666 =
                    let uu____79677 = FStar_Syntax_Syntax.as_arg tv1  in
                    [uu____79677]  in
                  FStar_Syntax_Util.mk_app
                    (FStar_Reflection_Data.refl_constant_term
                       FStar_Reflection_Data.fstar_refl_pack_ln) uu____79666
                   in
                term_as_mlexpr g t1)
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_monadic (m,uu____79704)) ->
           let t2 = FStar_Syntax_Subst.compress t1  in
           (match t2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) when
                FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname ->
                let uu____79737 =
                  let uu____79744 =
                    FStar_TypeChecker_Env.effect_decl_opt
                      g.FStar_Extraction_ML_UEnv.env_tcenv m
                     in
                  FStar_Util.must uu____79744  in
                (match uu____79737 with
                 | (ed,qualifiers) ->
                     let uu____79771 =
                       let uu____79773 =
                         FStar_TypeChecker_Env.is_reifiable_effect
                           g.FStar_Extraction_ML_UEnv.env_tcenv
                           ed.FStar_Syntax_Syntax.mname
                          in
                       Prims.op_Negation uu____79773  in
                     if uu____79771
                     then term_as_mlexpr g t2
                     else
                       failwith
                         "This should not happen (should have been handled at Tm_abs level)")
            | uu____79791 -> term_as_mlexpr g t2)
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____79793) -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____79799) -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____79805 =
             FStar_TypeChecker_TcTerm.type_of_tot_term
               g.FStar_Extraction_ML_UEnv.env_tcenv t
              in
           (match uu____79805 with
            | (uu____79818,ty,uu____79820) ->
                let ml_ty = term_as_mlty g ty  in
                let uu____79822 =
                  let uu____79823 =
                    FStar_Extraction_ML_Util.mlexpr_of_const
                      t.FStar_Syntax_Syntax.pos c
                     in
                  FStar_Extraction_ML_Syntax.with_ty ml_ty uu____79823  in
                (uu____79822, FStar_Extraction_ML_Syntax.E_PURE, ml_ty))
       | FStar_Syntax_Syntax.Tm_name uu____79824 ->
           let uu____79825 = is_type g t  in
           if uu____79825
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____79836 = FStar_Extraction_ML_UEnv.lookup_term g t  in
              match uu____79836 with
              | (FStar_Util.Inl uu____79849,uu____79850) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | (FStar_Util.Inr
                 { FStar_Extraction_ML_UEnv.exp_b_name = uu____79855;
                   FStar_Extraction_ML_UEnv.exp_b_expr = x;
                   FStar_Extraction_ML_UEnv.exp_b_tscheme = mltys;
                   FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____79858;_},qual)
                  ->
                  (match mltys with
                   | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                       ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | ([],t1) ->
                       let uu____79876 =
                         maybe_eta_data_and_project_record g qual t1 x  in
                       (uu____79876, FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | uu____79877 -> err_uninst g t mltys t))
       | FStar_Syntax_Syntax.Tm_fvar fv ->
           let uu____79885 = is_type g t  in
           if uu____79885
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____79896 = FStar_Extraction_ML_UEnv.try_lookup_fv g fv
                 in
              match uu____79896 with
              | FStar_Pervasives_Native.None  ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.MLTY_Erased)
              | FStar_Pervasives_Native.Some
                  { FStar_Extraction_ML_UEnv.exp_b_name = uu____79905;
                    FStar_Extraction_ML_UEnv.exp_b_expr = x;
                    FStar_Extraction_ML_UEnv.exp_b_tscheme = mltys;
                    FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____79908;_}
                  ->
                  (FStar_Extraction_ML_UEnv.debug g
                     (fun uu____79916  ->
                        let uu____79917 = FStar_Syntax_Print.fv_to_string fv
                           in
                        let uu____79919 =
                          FStar_Extraction_ML_Code.string_of_mlexpr
                            g.FStar_Extraction_ML_UEnv.currentModule x
                           in
                        let uu____79921 =
                          FStar_Extraction_ML_Code.string_of_mlty
                            g.FStar_Extraction_ML_UEnv.currentModule
                            (FStar_Pervasives_Native.snd mltys)
                           in
                        FStar_Util.print3 "looked up %s: got %s at %s \n"
                          uu____79917 uu____79919 uu____79921);
                   (match mltys with
                    | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                        ->
                        (FStar_Extraction_ML_Syntax.ml_unit,
                          FStar_Extraction_ML_Syntax.E_PURE, t1)
                    | ([],t1) ->
                        let uu____79934 =
                          maybe_eta_data_and_project_record g
                            fv.FStar_Syntax_Syntax.fv_qual t1 x
                           in
                        (uu____79934, FStar_Extraction_ML_Syntax.E_PURE, t1)
                    | uu____79935 -> err_uninst g t mltys t)))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,rcopt) ->
           let uu____79969 = FStar_Syntax_Subst.open_term bs body  in
           (match uu____79969 with
            | (bs1,body1) ->
                let uu____79982 = binders_as_ml_binders g bs1  in
                (match uu____79982 with
                 | (ml_bs,env) ->
                     let body2 =
                       match rcopt with
                       | FStar_Pervasives_Native.Some rc ->
                           let uu____80018 =
                             FStar_TypeChecker_Env.is_reifiable_rc
                               env.FStar_Extraction_ML_UEnv.env_tcenv rc
                              in
                           if uu____80018
                           then
                             FStar_TypeChecker_Util.reify_body
                               env.FStar_Extraction_ML_UEnv.env_tcenv body1
                           else body1
                       | FStar_Pervasives_Native.None  ->
                           (FStar_Extraction_ML_UEnv.debug g
                              (fun uu____80026  ->
                                 let uu____80027 =
                                   FStar_Syntax_Print.term_to_string body1
                                    in
                                 FStar_Util.print1
                                   "No computation type for: %s\n"
                                   uu____80027);
                            body1)
                        in
                     let uu____80030 = term_as_mlexpr env body2  in
                     (match uu____80030 with
                      | (ml_body,f,t1) ->
                          let uu____80046 =
                            FStar_List.fold_right
                              (fun uu____80066  ->
                                 fun uu____80067  ->
                                   match (uu____80066, uu____80067) with
                                   | ((uu____80090,targ),(f1,t2)) ->
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         (FStar_Extraction_ML_Syntax.MLTY_Fun
                                            (targ, f1, t2)))) ml_bs (f, t1)
                             in
                          (match uu____80046 with
                           | (f1,tfun) ->
                               let uu____80113 =
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty tfun)
                                   (FStar_Extraction_ML_Syntax.MLE_Fun
                                      (ml_bs, ml_body))
                                  in
                               (uu____80113, f1, tfun)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____80121;
              FStar_Syntax_Syntax.vars = uu____80122;_},(a1,uu____80124)::[])
           ->
           let ty =
             let uu____80164 =
               FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid  in
             term_as_mlty g uu____80164  in
           let uu____80165 =
             let uu____80166 =
               FStar_Extraction_ML_Util.mlexpr_of_range
                 a1.FStar_Syntax_Syntax.pos
                in
             FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty)
               uu____80166
              in
           (uu____80165, FStar_Extraction_ML_Syntax.E_PURE, ty)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____80167;
              FStar_Syntax_Syntax.vars = uu____80168;_},(t1,uu____80170)::
            (r,uu____80172)::[])
           -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____80227);
              FStar_Syntax_Syntax.pos = uu____80228;
              FStar_Syntax_Syntax.vars = uu____80229;_},uu____80230)
           -> failwith "Unreachable? Tm_app Const_reflect"
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let is_total rc =
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_Tot_lid)
               ||
               (FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
                  (FStar_List.existsb
                     (fun uu___619_80299  ->
                        match uu___619_80299 with
                        | FStar_Syntax_Syntax.TOTAL  -> true
                        | uu____80302 -> false)))
              in
           let uu____80304 =
             let uu____80309 =
               let uu____80310 = FStar_Syntax_Subst.compress head1  in
               uu____80310.FStar_Syntax_Syntax.n  in
             ((head1.FStar_Syntax_Syntax.n), uu____80309)  in
           (match uu____80304 with
            | (FStar_Syntax_Syntax.Tm_uvar uu____80319,uu____80320) ->
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
            | (uu____80334,FStar_Syntax_Syntax.Tm_abs
               (bs,uu____80336,FStar_Pervasives_Native.Some rc)) when
                is_total rc ->
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
            | (uu____80361,FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_reify )) ->
                let e =
                  let uu____80363 = FStar_List.hd args  in
                  FStar_TypeChecker_Util.reify_body_with_arg
                    g.FStar_Extraction_ML_UEnv.env_tcenv head1 uu____80363
                   in
                let tm =
                  let uu____80375 =
                    let uu____80380 = FStar_TypeChecker_Util.remove_reify e
                       in
                    let uu____80381 = FStar_List.tl args  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____80380 uu____80381  in
                  uu____80375 FStar_Pervasives_Native.None
                    t.FStar_Syntax_Syntax.pos
                   in
                term_as_mlexpr g tm
            | uu____80392 ->
                let rec extract_app is_data uu____80445 uu____80446 restArgs
                  =
                  match (uu____80445, uu____80446) with
                  | ((mlhead,mlargs_f),(f,t1)) ->
                      let mk_head uu____80527 =
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
                         (fun uu____80554  ->
                            let uu____80555 =
                              let uu____80557 = mk_head ()  in
                              FStar_Extraction_ML_Code.string_of_mlexpr
                                g.FStar_Extraction_ML_UEnv.currentModule
                                uu____80557
                               in
                            let uu____80558 =
                              FStar_Extraction_ML_Code.string_of_mlty
                                g.FStar_Extraction_ML_UEnv.currentModule t1
                               in
                            let uu____80560 =
                              match restArgs with
                              | [] -> "none"
                              | (hd1,uu____80571)::uu____80572 ->
                                  FStar_Syntax_Print.term_to_string hd1
                               in
                            FStar_Util.print3
                              "extract_app ml_head=%s type of head = %s, next arg = %s\n"
                              uu____80555 uu____80558 uu____80560);
                       (match (restArgs, t1) with
                        | ([],uu____80606) ->
                            let app =
                              let uu____80622 = mk_head ()  in
                              maybe_eta_data_and_project_record g is_data t1
                                uu____80622
                               in
                            (app, f, t1)
                        | ((arg,uu____80624)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                           (formal_t,f',t2)) when
                            (is_type g arg) &&
                              (type_leq g formal_t
                                 FStar_Extraction_ML_Syntax.ml_unit_ty)
                            ->
                            let uu____80655 =
                              let uu____80660 =
                                FStar_Extraction_ML_Util.join
                                  arg.FStar_Syntax_Syntax.pos f f'
                                 in
                              (uu____80660, t2)  in
                            extract_app is_data
                              (mlhead,
                                ((FStar_Extraction_ML_Syntax.ml_unit,
                                   FStar_Extraction_ML_Syntax.E_PURE) ::
                                mlargs_f)) uu____80655 rest
                        | ((e0,uu____80672)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                           (tExpected,f',t2)) ->
                            let r = e0.FStar_Syntax_Syntax.pos  in
                            let expected_effect =
                              let uu____80705 =
                                (FStar_Options.lax ()) &&
                                  (FStar_TypeChecker_Util.short_circuit_head
                                     head1)
                                 in
                              if uu____80705
                              then FStar_Extraction_ML_Syntax.E_IMPURE
                              else FStar_Extraction_ML_Syntax.E_PURE  in
                            let uu____80710 =
                              check_term_as_mlexpr g e0 expected_effect
                                tExpected
                               in
                            (match uu____80710 with
                             | (e01,tInferred) ->
                                 let uu____80723 =
                                   let uu____80728 =
                                     FStar_Extraction_ML_Util.join_l r
                                       [f; f']
                                      in
                                   (uu____80728, t2)  in
                                 extract_app is_data
                                   (mlhead, ((e01, expected_effect) ::
                                     mlargs_f)) uu____80723 rest)
                        | uu____80739 ->
                            let uu____80752 =
                              FStar_Extraction_ML_Util.udelta_unfold g t1  in
                            (match uu____80752 with
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
                                  | uu____80824 ->
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
                let extract_app_maybe_projector is_data mlhead uu____80895
                  args1 =
                  match uu____80895 with
                  | (f,t1) ->
                      (match is_data with
                       | FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_projector uu____80925)
                           ->
                           let rec remove_implicits args2 f1 t2 =
                             match (args2, t2) with
                             | ((a0,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____81009))::args3,FStar_Extraction_ML_Syntax.MLTY_Fun
                                (uu____81011,f',t3)) ->
                                 let uu____81049 =
                                   FStar_Extraction_ML_Util.join
                                     a0.FStar_Syntax_Syntax.pos f1 f'
                                    in
                                 remove_implicits args3 uu____81049 t3
                             | uu____81050 -> (args2, f1, t2)  in
                           let uu____81075 = remove_implicits args1 f t1  in
                           (match uu____81075 with
                            | (args2,f1,t2) ->
                                extract_app is_data (mlhead, []) (f1, t2)
                                  args2)
                       | uu____81131 ->
                           extract_app is_data (mlhead, []) (f, t1) args1)
                   in
                let extract_app_with_instantiations uu____81155 =
                  let head2 = FStar_Syntax_Util.un_uinst head1  in
                  match head2.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_name uu____81163 ->
                      let uu____81164 =
                        let uu____81185 =
                          FStar_Extraction_ML_UEnv.lookup_term g head2  in
                        match uu____81185 with
                        | (FStar_Util.Inr exp_b,q) ->
                            (FStar_Extraction_ML_UEnv.debug g
                               (fun uu____81224  ->
                                  let uu____81225 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  let uu____81227 =
                                    FStar_Extraction_ML_Code.string_of_mlexpr
                                      g.FStar_Extraction_ML_UEnv.currentModule
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_expr
                                     in
                                  let uu____81229 =
                                    FStar_Extraction_ML_Code.string_of_mlty
                                      g.FStar_Extraction_ML_UEnv.currentModule
                                      (FStar_Pervasives_Native.snd
                                         exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme)
                                     in
                                  let uu____81231 =
                                    FStar_Util.string_of_bool
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok
                                     in
                                  FStar_Util.print4
                                    "@@@looked up %s: got %s at %s (inst_ok=%s)\n"
                                    uu____81225 uu____81227 uu____81229
                                    uu____81231);
                             (((exp_b.FStar_Extraction_ML_UEnv.exp_b_expr),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok)),
                               q))
                        | uu____81258 -> failwith "FIXME Ty"  in
                      (match uu____81164 with
                       | ((head_ml,(vars,t1),inst_ok),qual) ->
                           let has_typ_apps =
                             match args with
                             | (a,uu____81334)::uu____81335 -> is_type g a
                             | uu____81362 -> false  in
                           let uu____81374 =
                             match vars with
                             | uu____81403::uu____81404 when
                                 (Prims.op_Negation has_typ_apps) && inst_ok
                                 -> (head_ml, t1, args)
                             | uu____81418 ->
                                 let n1 = FStar_List.length vars  in
                                 if n1 <= (FStar_List.length args)
                                 then
                                   let uu____81453 =
                                     FStar_Util.first_N n1 args  in
                                   (match uu____81453 with
                                    | (prefix1,rest) ->
                                        let prefixAsMLTypes =
                                          FStar_List.map
                                            (fun uu____81558  ->
                                               match uu____81558 with
                                               | (x,uu____81566) ->
                                                   term_as_mlty g x) prefix1
                                           in
                                        let t2 =
                                          instantiate (vars, t1)
                                            prefixAsMLTypes
                                           in
                                        (FStar_Extraction_ML_UEnv.debug g
                                           (fun uu____81578  ->
                                              let uu____81579 =
                                                FStar_Syntax_Print.term_to_string
                                                  head2
                                                 in
                                              let uu____81581 =
                                                FStar_Syntax_Print.args_to_string
                                                  prefix1
                                                 in
                                              let uu____81583 =
                                                let uu____81585 =
                                                  FStar_List.map
                                                    (FStar_Extraction_ML_Code.string_of_mlty
                                                       g.FStar_Extraction_ML_UEnv.currentModule)
                                                    prefixAsMLTypes
                                                   in
                                                FStar_All.pipe_right
                                                  uu____81585
                                                  (FStar_String.concat ", ")
                                                 in
                                              let uu____81595 =
                                                FStar_Extraction_ML_Code.string_of_mlty
                                                  g.FStar_Extraction_ML_UEnv.currentModule
                                                  t2
                                                 in
                                              FStar_Util.print4
                                                "@@@looked up %s, instantiated with [%s] translated to [%s], got %s\n"
                                                uu____81579 uu____81581
                                                uu____81583 uu____81595);
                                         (let mk_tapp e ty_args =
                                            match ty_args with
                                            | [] -> e
                                            | uu____81613 ->
                                                let uu___2233_81616 = e  in
                                                {
                                                  FStar_Extraction_ML_Syntax.expr
                                                    =
                                                    (FStar_Extraction_ML_Syntax.MLE_TApp
                                                       (e, ty_args));
                                                  FStar_Extraction_ML_Syntax.mlty
                                                    =
                                                    (uu___2233_81616.FStar_Extraction_ML_Syntax.mlty);
                                                  FStar_Extraction_ML_Syntax.loc
                                                    =
                                                    (uu___2233_81616.FStar_Extraction_ML_Syntax.loc)
                                                }
                                             in
                                          let head3 =
                                            match head_ml.FStar_Extraction_ML_Syntax.expr
                                            with
                                            | FStar_Extraction_ML_Syntax.MLE_Name
                                                uu____81620 ->
                                                let uu___2239_81621 =
                                                  mk_tapp head_ml
                                                    prefixAsMLTypes
                                                   in
                                                {
                                                  FStar_Extraction_ML_Syntax.expr
                                                    =
                                                    (uu___2239_81621.FStar_Extraction_ML_Syntax.expr);
                                                  FStar_Extraction_ML_Syntax.mlty
                                                    = t2;
                                                  FStar_Extraction_ML_Syntax.loc
                                                    =
                                                    (uu___2239_81621.FStar_Extraction_ML_Syntax.loc)
                                                }
                                            | FStar_Extraction_ML_Syntax.MLE_Var
                                                uu____81622 ->
                                                let uu___2239_81624 =
                                                  mk_tapp head_ml
                                                    prefixAsMLTypes
                                                   in
                                                {
                                                  FStar_Extraction_ML_Syntax.expr
                                                    =
                                                    (uu___2239_81624.FStar_Extraction_ML_Syntax.expr);
                                                  FStar_Extraction_ML_Syntax.mlty
                                                    = t2;
                                                  FStar_Extraction_ML_Syntax.loc
                                                    =
                                                    (uu___2239_81624.FStar_Extraction_ML_Syntax.loc)
                                                }
                                            | FStar_Extraction_ML_Syntax.MLE_App
                                                (head3,{
                                                         FStar_Extraction_ML_Syntax.expr
                                                           =
                                                           FStar_Extraction_ML_Syntax.MLE_Const
                                                           (FStar_Extraction_ML_Syntax.MLC_Unit
                                                           );
                                                         FStar_Extraction_ML_Syntax.mlty
                                                           = uu____81626;
                                                         FStar_Extraction_ML_Syntax.loc
                                                           = uu____81627;_}::[])
                                                ->
                                                FStar_All.pipe_right
                                                  (FStar_Extraction_ML_Syntax.MLE_App
                                                     ((let uu___2250_81633 =
                                                         mk_tapp head3
                                                           prefixAsMLTypes
                                                          in
                                                       {
                                                         FStar_Extraction_ML_Syntax.expr
                                                           =
                                                           (uu___2250_81633.FStar_Extraction_ML_Syntax.expr);
                                                         FStar_Extraction_ML_Syntax.mlty
                                                           =
                                                           (FStar_Extraction_ML_Syntax.MLTY_Fun
                                                              (FStar_Extraction_ML_Syntax.ml_unit_ty,
                                                                FStar_Extraction_ML_Syntax.E_PURE,
                                                                t2));
                                                         FStar_Extraction_ML_Syntax.loc
                                                           =
                                                           (uu___2250_81633.FStar_Extraction_ML_Syntax.loc)
                                                       }),
                                                       [FStar_Extraction_ML_Syntax.ml_unit]))
                                                  (FStar_Extraction_ML_Syntax.with_ty
                                                     t2)
                                            | uu____81634 ->
                                                failwith
                                                  "Impossible: Unexpected head term"
                                             in
                                          (head3, t2, rest))))
                                 else err_uninst g head2 (vars, t1) top
                              in
                           (match uu____81374 with
                            | (head_ml1,head_t,args1) ->
                                (match args1 with
                                 | [] ->
                                     let uu____81700 =
                                       maybe_eta_data_and_project_record g
                                         qual head_t head_ml1
                                        in
                                     (uu____81700,
                                       FStar_Extraction_ML_Syntax.E_PURE,
                                       head_t)
                                 | uu____81701 ->
                                     extract_app_maybe_projector qual
                                       head_ml1
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         head_t) args1)))
                  | FStar_Syntax_Syntax.Tm_fvar uu____81710 ->
                      let uu____81711 =
                        let uu____81732 =
                          FStar_Extraction_ML_UEnv.lookup_term g head2  in
                        match uu____81732 with
                        | (FStar_Util.Inr exp_b,q) ->
                            (FStar_Extraction_ML_UEnv.debug g
                               (fun uu____81771  ->
                                  let uu____81772 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  let uu____81774 =
                                    FStar_Extraction_ML_Code.string_of_mlexpr
                                      g.FStar_Extraction_ML_UEnv.currentModule
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_expr
                                     in
                                  let uu____81776 =
                                    FStar_Extraction_ML_Code.string_of_mlty
                                      g.FStar_Extraction_ML_UEnv.currentModule
                                      (FStar_Pervasives_Native.snd
                                         exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme)
                                     in
                                  let uu____81778 =
                                    FStar_Util.string_of_bool
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok
                                     in
                                  FStar_Util.print4
                                    "@@@looked up %s: got %s at %s (inst_ok=%s)\n"
                                    uu____81772 uu____81774 uu____81776
                                    uu____81778);
                             (((exp_b.FStar_Extraction_ML_UEnv.exp_b_expr),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok)),
                               q))
                        | uu____81805 -> failwith "FIXME Ty"  in
                      (match uu____81711 with
                       | ((head_ml,(vars,t1),inst_ok),qual) ->
                           let has_typ_apps =
                             match args with
                             | (a,uu____81881)::uu____81882 -> is_type g a
                             | uu____81909 -> false  in
                           let uu____81921 =
                             match vars with
                             | uu____81950::uu____81951 when
                                 (Prims.op_Negation has_typ_apps) && inst_ok
                                 -> (head_ml, t1, args)
                             | uu____81965 ->
                                 let n1 = FStar_List.length vars  in
                                 if n1 <= (FStar_List.length args)
                                 then
                                   let uu____82000 =
                                     FStar_Util.first_N n1 args  in
                                   (match uu____82000 with
                                    | (prefix1,rest) ->
                                        let prefixAsMLTypes =
                                          FStar_List.map
                                            (fun uu____82105  ->
                                               match uu____82105 with
                                               | (x,uu____82113) ->
                                                   term_as_mlty g x) prefix1
                                           in
                                        let t2 =
                                          instantiate (vars, t1)
                                            prefixAsMLTypes
                                           in
                                        (FStar_Extraction_ML_UEnv.debug g
                                           (fun uu____82125  ->
                                              let uu____82126 =
                                                FStar_Syntax_Print.term_to_string
                                                  head2
                                                 in
                                              let uu____82128 =
                                                FStar_Syntax_Print.args_to_string
                                                  prefix1
                                                 in
                                              let uu____82130 =
                                                let uu____82132 =
                                                  FStar_List.map
                                                    (FStar_Extraction_ML_Code.string_of_mlty
                                                       g.FStar_Extraction_ML_UEnv.currentModule)
                                                    prefixAsMLTypes
                                                   in
                                                FStar_All.pipe_right
                                                  uu____82132
                                                  (FStar_String.concat ", ")
                                                 in
                                              let uu____82142 =
                                                FStar_Extraction_ML_Code.string_of_mlty
                                                  g.FStar_Extraction_ML_UEnv.currentModule
                                                  t2
                                                 in
                                              FStar_Util.print4
                                                "@@@looked up %s, instantiated with [%s] translated to [%s], got %s\n"
                                                uu____82126 uu____82128
                                                uu____82130 uu____82142);
                                         (let mk_tapp e ty_args =
                                            match ty_args with
                                            | [] -> e
                                            | uu____82160 ->
                                                let uu___2233_82163 = e  in
                                                {
                                                  FStar_Extraction_ML_Syntax.expr
                                                    =
                                                    (FStar_Extraction_ML_Syntax.MLE_TApp
                                                       (e, ty_args));
                                                  FStar_Extraction_ML_Syntax.mlty
                                                    =
                                                    (uu___2233_82163.FStar_Extraction_ML_Syntax.mlty);
                                                  FStar_Extraction_ML_Syntax.loc
                                                    =
                                                    (uu___2233_82163.FStar_Extraction_ML_Syntax.loc)
                                                }
                                             in
                                          let head3 =
                                            match head_ml.FStar_Extraction_ML_Syntax.expr
                                            with
                                            | FStar_Extraction_ML_Syntax.MLE_Name
                                                uu____82167 ->
                                                let uu___2239_82168 =
                                                  mk_tapp head_ml
                                                    prefixAsMLTypes
                                                   in
                                                {
                                                  FStar_Extraction_ML_Syntax.expr
                                                    =
                                                    (uu___2239_82168.FStar_Extraction_ML_Syntax.expr);
                                                  FStar_Extraction_ML_Syntax.mlty
                                                    = t2;
                                                  FStar_Extraction_ML_Syntax.loc
                                                    =
                                                    (uu___2239_82168.FStar_Extraction_ML_Syntax.loc)
                                                }
                                            | FStar_Extraction_ML_Syntax.MLE_Var
                                                uu____82169 ->
                                                let uu___2239_82171 =
                                                  mk_tapp head_ml
                                                    prefixAsMLTypes
                                                   in
                                                {
                                                  FStar_Extraction_ML_Syntax.expr
                                                    =
                                                    (uu___2239_82171.FStar_Extraction_ML_Syntax.expr);
                                                  FStar_Extraction_ML_Syntax.mlty
                                                    = t2;
                                                  FStar_Extraction_ML_Syntax.loc
                                                    =
                                                    (uu___2239_82171.FStar_Extraction_ML_Syntax.loc)
                                                }
                                            | FStar_Extraction_ML_Syntax.MLE_App
                                                (head3,{
                                                         FStar_Extraction_ML_Syntax.expr
                                                           =
                                                           FStar_Extraction_ML_Syntax.MLE_Const
                                                           (FStar_Extraction_ML_Syntax.MLC_Unit
                                                           );
                                                         FStar_Extraction_ML_Syntax.mlty
                                                           = uu____82173;
                                                         FStar_Extraction_ML_Syntax.loc
                                                           = uu____82174;_}::[])
                                                ->
                                                FStar_All.pipe_right
                                                  (FStar_Extraction_ML_Syntax.MLE_App
                                                     ((let uu___2250_82180 =
                                                         mk_tapp head3
                                                           prefixAsMLTypes
                                                          in
                                                       {
                                                         FStar_Extraction_ML_Syntax.expr
                                                           =
                                                           (uu___2250_82180.FStar_Extraction_ML_Syntax.expr);
                                                         FStar_Extraction_ML_Syntax.mlty
                                                           =
                                                           (FStar_Extraction_ML_Syntax.MLTY_Fun
                                                              (FStar_Extraction_ML_Syntax.ml_unit_ty,
                                                                FStar_Extraction_ML_Syntax.E_PURE,
                                                                t2));
                                                         FStar_Extraction_ML_Syntax.loc
                                                           =
                                                           (uu___2250_82180.FStar_Extraction_ML_Syntax.loc)
                                                       }),
                                                       [FStar_Extraction_ML_Syntax.ml_unit]))
                                                  (FStar_Extraction_ML_Syntax.with_ty
                                                     t2)
                                            | uu____82181 ->
                                                failwith
                                                  "Impossible: Unexpected head term"
                                             in
                                          (head3, t2, rest))))
                                 else err_uninst g head2 (vars, t1) top
                              in
                           (match uu____81921 with
                            | (head_ml1,head_t,args1) ->
                                (match args1 with
                                 | [] ->
                                     let uu____82247 =
                                       maybe_eta_data_and_project_record g
                                         qual head_t head_ml1
                                        in
                                     (uu____82247,
                                       FStar_Extraction_ML_Syntax.E_PURE,
                                       head_t)
                                 | uu____82248 ->
                                     extract_app_maybe_projector qual
                                       head_ml1
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         head_t) args1)))
                  | uu____82257 ->
                      let uu____82258 = term_as_mlexpr g head2  in
                      (match uu____82258 with
                       | (head3,f,t1) ->
                           extract_app_maybe_projector
                             FStar_Pervasives_Native.None head3 (f, t1) args)
                   in
                let uu____82274 = is_type g t  in
                if uu____82274
                then
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
                else
                  (let uu____82285 =
                     let uu____82286 = FStar_Syntax_Util.un_uinst head1  in
                     uu____82286.FStar_Syntax_Syntax.n  in
                   match uu____82285 with
                   | FStar_Syntax_Syntax.Tm_fvar fv ->
                       let uu____82296 =
                         FStar_Extraction_ML_UEnv.try_lookup_fv g fv  in
                       (match uu____82296 with
                        | FStar_Pervasives_Native.None  ->
                            (FStar_Extraction_ML_Syntax.ml_unit,
                              FStar_Extraction_ML_Syntax.E_PURE,
                              FStar_Extraction_ML_Syntax.MLTY_Erased)
                        | uu____82305 -> extract_app_with_instantiations ())
                   | uu____82308 -> extract_app_with_instantiations ()))
       | FStar_Syntax_Syntax.Tm_ascribed (e0,(tc,uu____82311),f) ->
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
           let uu____82379 = check_term_as_mlexpr g e0 f1 t1  in
           (match uu____82379 with | (e,t2) -> (e, f1, t2))
       | FStar_Syntax_Syntax.Tm_let ((is_rec,lbs),e') ->
           let top_level = FStar_Syntax_Syntax.is_top_level lbs  in
           let uu____82414 =
             if is_rec
             then FStar_Syntax_Subst.open_let_rec lbs e'
             else
               (let uu____82430 = FStar_Syntax_Syntax.is_top_level lbs  in
                if uu____82430
                then (lbs, e')
                else
                  (let lb = FStar_List.hd lbs  in
                   let x =
                     let uu____82445 =
                       FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                     FStar_Syntax_Syntax.freshen_bv uu____82445  in
                   let lb1 =
                     let uu___2301_82447 = lb  in
                     {
                       FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                       FStar_Syntax_Syntax.lbunivs =
                         (uu___2301_82447.FStar_Syntax_Syntax.lbunivs);
                       FStar_Syntax_Syntax.lbtyp =
                         (uu___2301_82447.FStar_Syntax_Syntax.lbtyp);
                       FStar_Syntax_Syntax.lbeff =
                         (uu___2301_82447.FStar_Syntax_Syntax.lbeff);
                       FStar_Syntax_Syntax.lbdef =
                         (uu___2301_82447.FStar_Syntax_Syntax.lbdef);
                       FStar_Syntax_Syntax.lbattrs =
                         (uu___2301_82447.FStar_Syntax_Syntax.lbattrs);
                       FStar_Syntax_Syntax.lbpos =
                         (uu___2301_82447.FStar_Syntax_Syntax.lbpos)
                     }  in
                   let e'1 =
                     FStar_Syntax_Subst.subst
                       [FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x)] e'
                      in
                   ([lb1], e'1)))
              in
           (match uu____82414 with
            | (lbs1,e'1) ->
                let lbs2 =
                  if top_level
                  then
                    FStar_All.pipe_right lbs1
                      (FStar_List.map
                         (fun lb  ->
                            let tcenv =
                              let uu____82481 =
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
                                uu____82481
                               in
                            let lbdef =
                              let uu____82496 = FStar_Options.ml_ish ()  in
                              if uu____82496
                              then lb.FStar_Syntax_Syntax.lbdef
                              else
                                (let norm_call uu____82508 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.AllowUnboundUniverses;
                                     FStar_TypeChecker_Env.EraseUniverses;
                                     FStar_TypeChecker_Env.Inlining;
                                     FStar_TypeChecker_Env.Eager_unfolding;
                                     FStar_TypeChecker_Env.Exclude
                                       FStar_TypeChecker_Env.Zeta;
                                     FStar_TypeChecker_Env.PureSubtermsWithinComputations;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.Unascribe;
                                     FStar_TypeChecker_Env.ForExtraction]
                                     tcenv lb.FStar_Syntax_Syntax.lbdef
                                    in
                                 let uu____82509 =
                                   (FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug tcenv)
                                      (FStar_Options.Other "Extraction"))
                                     ||
                                     (FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug tcenv)
                                        (FStar_Options.Other "ExtractNorm"))
                                    in
                                 if uu____82509
                                 then
                                   ((let uu____82519 =
                                       FStar_Syntax_Print.lbname_to_string
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     let uu____82521 =
                                       FStar_Syntax_Print.term_to_string
                                         lb.FStar_Syntax_Syntax.lbdef
                                        in
                                     FStar_Util.print2
                                       "Starting to normalize top-level let %s)\n\tlbdef=%s"
                                       uu____82519 uu____82521);
                                    (let a =
                                       let uu____82527 =
                                         let uu____82529 =
                                           FStar_Syntax_Print.lbname_to_string
                                             lb.FStar_Syntax_Syntax.lbname
                                            in
                                         FStar_Util.format1
                                           "###(Time to normalize top-level let %s)"
                                           uu____82529
                                          in
                                       FStar_Util.measure_execution_time
                                         uu____82527 norm_call
                                        in
                                     (let uu____82535 =
                                        FStar_Syntax_Print.term_to_string a
                                         in
                                      FStar_Util.print1 "Normalized to %s\n"
                                        uu____82535);
                                     a))
                                 else norm_call ())
                               in
                            let uu___2319_82540 = lb  in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___2319_82540.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___2319_82540.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp =
                                (uu___2319_82540.FStar_Syntax_Syntax.lbtyp);
                              FStar_Syntax_Syntax.lbeff =
                                (uu___2319_82540.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = lbdef;
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___2319_82540.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___2319_82540.FStar_Syntax_Syntax.lbpos)
                            }))
                  else lbs1  in
                let check_lb env uu____82593 =
                  match uu____82593 with
                  | (nm,(_lbname,f,(_t,(targs,polytype)),add_unit,e)) ->
                      let env1 =
                        FStar_List.fold_left
                          (fun env1  ->
                             fun uu____82749  ->
                               match uu____82749 with
                               | (a,uu____82757) ->
                                   FStar_Extraction_ML_UEnv.extend_ty env1 a
                                     FStar_Pervasives_Native.None) env targs
                         in
                      let expected_t = FStar_Pervasives_Native.snd polytype
                         in
                      let uu____82763 =
                        check_term_as_mlexpr env1 e f expected_t  in
                      (match uu____82763 with
                       | (e1,ty) ->
                           let uu____82774 =
                             maybe_promote_effect e1 f expected_t  in
                           (match uu____82774 with
                            | (e2,f1) ->
                                let meta =
                                  match (f1, ty) with
                                  | (FStar_Extraction_ML_Syntax.E_PURE
                                     ,FStar_Extraction_ML_Syntax.MLTY_Erased
                                     ) -> [FStar_Extraction_ML_Syntax.Erased]
                                  | (FStar_Extraction_ML_Syntax.E_GHOST
                                     ,FStar_Extraction_ML_Syntax.MLTY_Erased
                                     ) -> [FStar_Extraction_ML_Syntax.Erased]
                                  | uu____82786 -> []  in
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
                let uu____82817 =
                  FStar_List.fold_right
                    (fun lb  ->
                       fun uu____82914  ->
                         match uu____82914 with
                         | (env,lbs4) ->
                             let uu____83048 = lb  in
                             (match uu____83048 with
                              | (lbname,uu____83099,(t1,(uu____83101,polytype)),add_unit,uu____83104)
                                  ->
                                  let uu____83119 =
                                    FStar_Extraction_ML_UEnv.extend_lb env
                                      lbname t1 polytype add_unit true
                                     in
                                  (match uu____83119 with
                                   | (env1,nm,uu____83160) ->
                                       (env1, ((nm, lb) :: lbs4))))) lbs3
                    (g, [])
                   in
                (match uu____82817 with
                 | (env_body,lbs4) ->
                     let env_def = if is_rec then env_body else g  in
                     let lbs5 =
                       FStar_All.pipe_right lbs4
                         (FStar_List.map (check_lb env_def))
                        in
                     let e'_rng = e'1.FStar_Syntax_Syntax.pos  in
                     let uu____83439 = term_as_mlexpr env_body e'1  in
                     (match uu____83439 with
                      | (e'2,f',t') ->
                          let f =
                            let uu____83456 =
                              let uu____83459 =
                                FStar_List.map FStar_Pervasives_Native.fst
                                  lbs5
                                 in
                              f' :: uu____83459  in
                            FStar_Extraction_ML_Util.join_l e'_rng
                              uu____83456
                             in
                          let is_rec1 =
                            if is_rec = true
                            then FStar_Extraction_ML_Syntax.Rec
                            else FStar_Extraction_ML_Syntax.NonRec  in
                          let uu____83472 =
                            let uu____83473 =
                              let uu____83474 =
                                let uu____83475 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    lbs5
                                   in
                                (is_rec1, uu____83475)  in
                              mk_MLE_Let top_level uu____83474 e'2  in
                            let uu____83484 =
                              FStar_Extraction_ML_Util.mlloc_of_range
                                t.FStar_Syntax_Syntax.pos
                               in
                            FStar_Extraction_ML_Syntax.with_ty_loc t'
                              uu____83473 uu____83484
                             in
                          (uu____83472, f, t'))))
       | FStar_Syntax_Syntax.Tm_match (scrutinee,pats) ->
           let uu____83523 = term_as_mlexpr g scrutinee  in
           (match uu____83523 with
            | (e,f_e,t_e) ->
                let uu____83539 = check_pats_for_ite pats  in
                (match uu____83539 with
                 | (b,then_e,else_e) ->
                     let no_lift x t1 = x  in
                     if b
                     then
                       (match (then_e, else_e) with
                        | (FStar_Pervasives_Native.Some
                           then_e1,FStar_Pervasives_Native.Some else_e1) ->
                            let uu____83604 = term_as_mlexpr g then_e1  in
                            (match uu____83604 with
                             | (then_mle,f_then,t_then) ->
                                 let uu____83620 = term_as_mlexpr g else_e1
                                    in
                                 (match uu____83620 with
                                  | (else_mle,f_else,t_else) ->
                                      let uu____83636 =
                                        let uu____83647 =
                                          type_leq g t_then t_else  in
                                        if uu____83647
                                        then (t_else, no_lift)
                                        else
                                          (let uu____83668 =
                                             type_leq g t_else t_then  in
                                           if uu____83668
                                           then (t_then, no_lift)
                                           else
                                             (FStar_Extraction_ML_Syntax.MLTY_Top,
                                               FStar_Extraction_ML_Syntax.apply_obj_repr))
                                         in
                                      (match uu____83636 with
                                       | (t_branch,maybe_lift1) ->
                                           let uu____83715 =
                                             let uu____83716 =
                                               let uu____83717 =
                                                 let uu____83726 =
                                                   maybe_lift1 then_mle
                                                     t_then
                                                    in
                                                 let uu____83727 =
                                                   let uu____83730 =
                                                     maybe_lift1 else_mle
                                                       t_else
                                                      in
                                                   FStar_Pervasives_Native.Some
                                                     uu____83730
                                                    in
                                                 (e, uu____83726,
                                                   uu____83727)
                                                  in
                                               FStar_Extraction_ML_Syntax.MLE_If
                                                 uu____83717
                                                in
                                             FStar_All.pipe_left
                                               (FStar_Extraction_ML_Syntax.with_ty
                                                  t_branch) uu____83716
                                              in
                                           let uu____83733 =
                                             FStar_Extraction_ML_Util.join
                                               then_e1.FStar_Syntax_Syntax.pos
                                               f_then f_else
                                              in
                                           (uu____83715, uu____83733,
                                             t_branch))))
                        | uu____83734 ->
                            failwith
                              "ITE pats matched but then and else expressions not found?")
                     else
                       (let uu____83752 =
                          FStar_All.pipe_right pats
                            (FStar_Util.fold_map
                               (fun compat  ->
                                  fun br  ->
                                    let uu____83851 =
                                      FStar_Syntax_Subst.open_branch br  in
                                    match uu____83851 with
                                    | (pat,when_opt,branch1) ->
                                        let uu____83896 =
                                          extract_pat g pat t_e
                                            term_as_mlexpr
                                           in
                                        (match uu____83896 with
                                         | (env,p,pat_t_compat) ->
                                             let uu____83958 =
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
                                                   let uu____83981 =
                                                     term_as_mlexpr env w  in
                                                   (match uu____83981 with
                                                    | (w1,f_w,t_w) ->
                                                        let w2 =
                                                          maybe_coerce w_pos
                                                            env w1 t_w
                                                            FStar_Extraction_ML_Syntax.ml_bool_ty
                                                           in
                                                        ((FStar_Pervasives_Native.Some
                                                            w2), f_w))
                                                in
                                             (match uu____83958 with
                                              | (when_opt1,f_when) ->
                                                  let uu____84031 =
                                                    term_as_mlexpr env
                                                      branch1
                                                     in
                                                  (match uu____84031 with
                                                   | (mlbranch,f_branch,t_branch)
                                                       ->
                                                       let uu____84066 =
                                                         FStar_All.pipe_right
                                                           p
                                                           (FStar_List.map
                                                              (fun
                                                                 uu____84143 
                                                                 ->
                                                                 match uu____84143
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
                                                         uu____84066)))))
                               true)
                           in
                        match uu____83752 with
                        | (pat_t_compat,mlbranches) ->
                            let mlbranches1 = FStar_List.flatten mlbranches
                               in
                            let e1 =
                              if pat_t_compat
                              then e
                              else
                                (FStar_Extraction_ML_UEnv.debug g
                                   (fun uu____84314  ->
                                      let uu____84315 =
                                        FStar_Extraction_ML_Code.string_of_mlexpr
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          e
                                         in
                                      let uu____84317 =
                                        FStar_Extraction_ML_Code.string_of_mlty
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          t_e
                                         in
                                      FStar_Util.print2
                                        "Coercing scrutinee %s from type %s because pattern type is incompatible\n"
                                        uu____84315 uu____84317);
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty t_e)
                                   (FStar_Extraction_ML_Syntax.MLE_Coerce
                                      (e, t_e,
                                        FStar_Extraction_ML_Syntax.MLTY_Top)))
                               in
                            (match mlbranches1 with
                             | [] ->
                                 let uu____84344 =
                                   let uu____84345 =
                                     FStar_Syntax_Syntax.lid_as_fv
                                       FStar_Parser_Const.failwith_lid
                                       FStar_Syntax_Syntax.delta_constant
                                       FStar_Pervasives_Native.None
                                      in
                                   FStar_Extraction_ML_UEnv.lookup_fv g
                                     uu____84345
                                    in
                                 (match uu____84344 with
                                  | {
                                      FStar_Extraction_ML_UEnv.exp_b_name =
                                        uu____84352;
                                      FStar_Extraction_ML_UEnv.exp_b_expr =
                                        fw;
                                      FStar_Extraction_ML_UEnv.exp_b_tscheme
                                        = uu____84354;
                                      FStar_Extraction_ML_UEnv.exp_b_inst_ok
                                        = uu____84355;_}
                                      ->
                                      let uu____84358 =
                                        let uu____84359 =
                                          let uu____84360 =
                                            let uu____84367 =
                                              let uu____84370 =
                                                FStar_All.pipe_left
                                                  (FStar_Extraction_ML_Syntax.with_ty
                                                     FStar_Extraction_ML_Syntax.ml_string_ty)
                                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                                     (FStar_Extraction_ML_Syntax.MLC_String
                                                        "unreachable"))
                                                 in
                                              [uu____84370]  in
                                            (fw, uu____84367)  in
                                          FStar_Extraction_ML_Syntax.MLE_App
                                            uu____84360
                                           in
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             FStar_Extraction_ML_Syntax.ml_int_ty)
                                          uu____84359
                                         in
                                      (uu____84358,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        FStar_Extraction_ML_Syntax.ml_int_ty))
                             | (uu____84374,uu____84375,(uu____84376,f_first,t_first))::rest
                                 ->
                                 let uu____84436 =
                                   FStar_List.fold_left
                                     (fun uu____84478  ->
                                        fun uu____84479  ->
                                          match (uu____84478, uu____84479)
                                          with
                                          | ((topt,f),(uu____84536,uu____84537,
                                                       (uu____84538,f_branch,t_branch)))
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
                                                    let uu____84594 =
                                                      type_leq g t1 t_branch
                                                       in
                                                    if uu____84594
                                                    then
                                                      FStar_Pervasives_Native.Some
                                                        t_branch
                                                    else
                                                      (let uu____84601 =
                                                         type_leq g t_branch
                                                           t1
                                                          in
                                                       if uu____84601
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
                                 (match uu____84436 with
                                  | (topt,f_match) ->
                                      let mlbranches2 =
                                        FStar_All.pipe_right mlbranches1
                                          (FStar_List.map
                                             (fun uu____84699  ->
                                                match uu____84699 with
                                                | (p,(wopt,uu____84728),
                                                   (b1,uu____84730,t1)) ->
                                                    let b2 =
                                                      match topt with
                                                      | FStar_Pervasives_Native.None
                                                           ->
                                                          FStar_Extraction_ML_Syntax.apply_obj_repr
                                                            b1 t1
                                                      | FStar_Pervasives_Native.Some
                                                          uu____84749 -> b1
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
                                      let uu____84754 =
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             t_match)
                                          (FStar_Extraction_ML_Syntax.MLE_Match
                                             (e1, mlbranches2))
                                         in
                                      (uu____84754, f_match, t_match)))))))

let (ind_discriminator_body :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlmodule1)
  =
  fun env  ->
    fun discName  ->
      fun constrName  ->
        let uu____84781 =
          let uu____84786 =
            FStar_TypeChecker_Env.lookup_lid
              env.FStar_Extraction_ML_UEnv.env_tcenv discName
             in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____84786  in
        match uu____84781 with
        | (uu____84811,fstar_disc_type) ->
            let wildcards =
              let uu____84821 =
                let uu____84822 = FStar_Syntax_Subst.compress fstar_disc_type
                   in
                uu____84822.FStar_Syntax_Syntax.n  in
              match uu____84821 with
              | FStar_Syntax_Syntax.Tm_arrow (binders,uu____84833) ->
                  let uu____84854 =
                    FStar_All.pipe_right binders
                      (FStar_List.filter
                         (fun uu___620_84888  ->
                            match uu___620_84888 with
                            | (uu____84896,FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____84897)) ->
                                true
                            | uu____84902 -> false))
                     in
                  FStar_All.pipe_right uu____84854
                    (FStar_List.map
                       (fun uu____84938  ->
                          let uu____84945 = fresh "_"  in
                          (uu____84945, FStar_Extraction_ML_Syntax.MLTY_Top)))
              | uu____84949 -> failwith "Discriminator must be a function"
               in
            let mlid = fresh "_discr_"  in
            let targ = FStar_Extraction_ML_Syntax.MLTY_Top  in
            let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top  in
            let discrBody =
              let uu____84964 =
                let uu____84965 =
                  let uu____84977 =
                    let uu____84978 =
                      let uu____84979 =
                        let uu____84994 =
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty targ)
                            (FStar_Extraction_ML_Syntax.MLE_Name ([], mlid))
                           in
                        let uu____85000 =
                          let uu____85011 =
                            let uu____85020 =
                              let uu____85021 =
                                let uu____85028 =
                                  FStar_Extraction_ML_Syntax.mlpath_of_lident
                                    constrName
                                   in
                                (uu____85028,
                                  [FStar_Extraction_ML_Syntax.MLP_Wild])
                                 in
                              FStar_Extraction_ML_Syntax.MLP_CTor uu____85021
                               in
                            let uu____85031 =
                              FStar_All.pipe_left
                                (FStar_Extraction_ML_Syntax.with_ty
                                   FStar_Extraction_ML_Syntax.ml_bool_ty)
                                (FStar_Extraction_ML_Syntax.MLE_Const
                                   (FStar_Extraction_ML_Syntax.MLC_Bool true))
                               in
                            (uu____85020, FStar_Pervasives_Native.None,
                              uu____85031)
                             in
                          let uu____85035 =
                            let uu____85046 =
                              let uu____85055 =
                                FStar_All.pipe_left
                                  (FStar_Extraction_ML_Syntax.with_ty
                                     FStar_Extraction_ML_Syntax.ml_bool_ty)
                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                     (FStar_Extraction_ML_Syntax.MLC_Bool
                                        false))
                                 in
                              (FStar_Extraction_ML_Syntax.MLP_Wild,
                                FStar_Pervasives_Native.None, uu____85055)
                               in
                            [uu____85046]  in
                          uu____85011 :: uu____85035  in
                        (uu____84994, uu____85000)  in
                      FStar_Extraction_ML_Syntax.MLE_Match uu____84979  in
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.ml_bool_ty) uu____84978
                     in
                  ((FStar_List.append wildcards [(mlid, targ)]), uu____84977)
                   in
                FStar_Extraction_ML_Syntax.MLE_Fun uu____84965  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty disc_ty) uu____84964
               in
            let uu____85116 =
              let uu____85117 =
                let uu____85120 =
                  let uu____85121 =
                    FStar_Extraction_ML_UEnv.convIdent
                      discName.FStar_Ident.ident
                     in
                  {
                    FStar_Extraction_ML_Syntax.mllb_name = uu____85121;
                    FStar_Extraction_ML_Syntax.mllb_tysc =
                      FStar_Pervasives_Native.None;
                    FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                    FStar_Extraction_ML_Syntax.mllb_def = discrBody;
                    FStar_Extraction_ML_Syntax.mllb_meta = [];
                    FStar_Extraction_ML_Syntax.print_typ = false
                  }  in
                [uu____85120]  in
              (FStar_Extraction_ML_Syntax.NonRec, uu____85117)  in
            FStar_Extraction_ML_Syntax.MLM_Let uu____85116
  