open Prims
exception Un_extractable 
let (uu___is_Un_extractable : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Un_extractable  -> true | uu____70767 -> false
  
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
  'Auu____70836 .
    FStar_Ident.ident Prims.list ->
      'Auu____70836 Prims.list -> (Prims.string * 'Auu____70836) Prims.list
  =
  fun fs  ->
    fun vs  ->
      FStar_List.map2 (fun f  -> fun e  -> ((f.FStar_Ident.idText), e)) fs vs
  
let fail :
  'Auu____70879 .
    FStar_Range.range ->
      (FStar_Errors.raw_error * Prims.string) -> 'Auu____70879
  = fun r  -> fun err  -> FStar_Errors.raise_error err r 
let err_uninst :
  'Auu____70911 .
    FStar_Extraction_ML_UEnv.uenv ->
      FStar_Syntax_Syntax.term ->
        (Prims.string Prims.list * FStar_Extraction_ML_Syntax.mlty) ->
          FStar_Syntax_Syntax.term -> 'Auu____70911
  =
  fun env  ->
    fun t  ->
      fun uu____70937  ->
        fun app  ->
          match uu____70937 with
          | (vars,ty) ->
              let uu____70954 =
                let uu____70960 =
                  let uu____70962 = FStar_Syntax_Print.term_to_string t  in
                  let uu____70964 =
                    FStar_All.pipe_right vars (FStar_String.concat ", ")  in
                  let uu____70971 =
                    FStar_Extraction_ML_Code.string_of_mlty
                      env.FStar_Extraction_ML_UEnv.currentModule ty
                     in
                  let uu____70973 = FStar_Syntax_Print.term_to_string app  in
                  FStar_Util.format4
                    "Variable %s has a polymorphic type (forall %s. %s); expected it to be fully instantiated, but got %s"
                    uu____70962 uu____70964 uu____70971 uu____70973
                   in
                (FStar_Errors.Fatal_Uninstantiated, uu____70960)  in
              fail t.FStar_Syntax_Syntax.pos uu____70954
  
let err_ill_typed_application :
  'Auu____70992 'Auu____70993 .
    FStar_Extraction_ML_UEnv.uenv ->
      FStar_Syntax_Syntax.term ->
        FStar_Extraction_ML_Syntax.mlexpr ->
          (FStar_Syntax_Syntax.term * 'Auu____70992) Prims.list ->
            FStar_Extraction_ML_Syntax.mlty -> 'Auu____70993
  =
  fun env  ->
    fun t  ->
      fun mlhead  ->
        fun args  ->
          fun ty  ->
            let uu____71031 =
              let uu____71037 =
                let uu____71039 = FStar_Syntax_Print.term_to_string t  in
                let uu____71041 =
                  FStar_Extraction_ML_Code.string_of_mlexpr
                    env.FStar_Extraction_ML_UEnv.currentModule mlhead
                   in
                let uu____71043 =
                  FStar_Extraction_ML_Code.string_of_mlty
                    env.FStar_Extraction_ML_UEnv.currentModule ty
                   in
                let uu____71045 =
                  let uu____71047 =
                    FStar_All.pipe_right args
                      (FStar_List.map
                         (fun uu____71068  ->
                            match uu____71068 with
                            | (x,uu____71075) ->
                                FStar_Syntax_Print.term_to_string x))
                     in
                  FStar_All.pipe_right uu____71047 (FStar_String.concat " ")
                   in
                FStar_Util.format4
                  "Ill-typed application: source application is %s \n translated prefix to %s at type %s\n remaining args are %s\n"
                  uu____71039 uu____71041 uu____71043 uu____71045
                 in
              (FStar_Errors.Fatal_IllTyped, uu____71037)  in
            fail t.FStar_Syntax_Syntax.pos uu____71031
  
let err_ill_typed_erasure :
  'Auu____71092 .
    FStar_Extraction_ML_UEnv.uenv ->
      FStar_Range.range -> FStar_Extraction_ML_Syntax.mlty -> 'Auu____71092
  =
  fun env  ->
    fun pos  ->
      fun ty  ->
        let uu____71108 =
          let uu____71114 =
            let uu____71116 =
              FStar_Extraction_ML_Code.string_of_mlty
                env.FStar_Extraction_ML_UEnv.currentModule ty
               in
            FStar_Util.format1
              "Erased value found where a value of type %s was expected"
              uu____71116
             in
          (FStar_Errors.Fatal_IllTyped, uu____71114)  in
        fail pos uu____71108
  
let err_value_restriction :
  'Auu____71125 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> 'Auu____71125
  =
  fun t  ->
    let uu____71135 =
      let uu____71141 =
        let uu____71143 = FStar_Syntax_Print.tag_of_term t  in
        let uu____71145 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format2
          "Refusing to generalize because of the value restriction: (%s) %s"
          uu____71143 uu____71145
         in
      (FStar_Errors.Fatal_ValueRestriction, uu____71141)  in
    fail t.FStar_Syntax_Syntax.pos uu____71135
  
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
            let uu____71179 =
              let uu____71185 =
                let uu____71187 = FStar_Syntax_Print.term_to_string t  in
                let uu____71189 =
                  FStar_Extraction_ML_Code.string_of_mlty
                    env.FStar_Extraction_ML_UEnv.currentModule ty
                   in
                let uu____71191 = FStar_Extraction_ML_Util.eff_to_string f0
                   in
                let uu____71193 = FStar_Extraction_ML_Util.eff_to_string f1
                   in
                FStar_Util.format4
                  "for expression %s of type %s, Expected effect %s; got effect %s"
                  uu____71187 uu____71189 uu____71191 uu____71193
                 in
              (FStar_Errors.Warning_ExtractionUnexpectedEffect, uu____71185)
               in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____71179
  
let (effect_as_etag :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Ident.lident -> FStar_Extraction_ML_Syntax.e_tag)
  =
  let cache = FStar_Util.smap_create (Prims.parse_int "20")  in
  let rec delta_norm_eff g l =
    let uu____71221 = FStar_Util.smap_try_find cache l.FStar_Ident.str  in
    match uu____71221 with
    | FStar_Pervasives_Native.Some l1 -> l1
    | FStar_Pervasives_Native.None  ->
        let res =
          let uu____71226 =
            FStar_TypeChecker_Env.lookup_effect_abbrev
              g.FStar_Extraction_ML_UEnv.env_tcenv
              [FStar_Syntax_Syntax.U_zero] l
             in
          match uu____71226 with
          | FStar_Pervasives_Native.None  -> l
          | FStar_Pervasives_Native.Some (uu____71237,c) ->
              delta_norm_eff g (FStar_Syntax_Util.comp_effect_name c)
           in
        (FStar_Util.smap_add cache l.FStar_Ident.str res; res)
     in
  fun g  ->
    fun l  ->
      let l1 = delta_norm_eff g l  in
      let uu____71247 =
        FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid  in
      if uu____71247
      then FStar_Extraction_ML_Syntax.E_PURE
      else
        (let uu____71252 =
           FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GHOST_lid  in
         if uu____71252
         then FStar_Extraction_ML_Syntax.E_GHOST
         else
           (let ed_opt =
              FStar_TypeChecker_Env.effect_decl_opt
                g.FStar_Extraction_ML_UEnv.env_tcenv l1
               in
            match ed_opt with
            | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                let uu____71278 =
                  FStar_TypeChecker_Env.is_reifiable_effect
                    g.FStar_Extraction_ML_UEnv.env_tcenv
                    ed.FStar_Syntax_Syntax.mname
                   in
                if uu____71278
                then FStar_Extraction_ML_Syntax.E_PURE
                else FStar_Extraction_ML_Syntax.E_IMPURE
            | FStar_Pervasives_Native.None  ->
                FStar_Extraction_ML_Syntax.E_IMPURE))
  
let rec (is_arity :
  FStar_Extraction_ML_UEnv.uenv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t  in
      let uu____71302 =
        let uu____71303 = FStar_Syntax_Subst.compress t1  in
        uu____71303.FStar_Syntax_Syntax.n  in
      match uu____71302 with
      | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____71309 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_ascribed uu____71334 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_meta uu____71363 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____71373 = FStar_Syntax_Util.unfold_lazy i  in
          is_arity env uu____71373
      | FStar_Syntax_Syntax.Tm_uvar uu____71374 -> false
      | FStar_Syntax_Syntax.Tm_constant uu____71388 -> false
      | FStar_Syntax_Syntax.Tm_name uu____71390 -> false
      | FStar_Syntax_Syntax.Tm_quoted uu____71392 -> false
      | FStar_Syntax_Syntax.Tm_bvar uu____71400 -> false
      | FStar_Syntax_Syntax.Tm_type uu____71402 -> true
      | FStar_Syntax_Syntax.Tm_arrow (uu____71404,c) ->
          is_arity env (FStar_Syntax_Util.comp_result c)
      | FStar_Syntax_Syntax.Tm_fvar uu____71426 ->
          let t2 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Env.AllowUnboundUniverses;
              FStar_TypeChecker_Env.EraseUniverses;
              FStar_TypeChecker_Env.UnfoldUntil
                FStar_Syntax_Syntax.delta_constant]
              env.FStar_Extraction_ML_UEnv.env_tcenv t1
             in
          let uu____71428 =
            let uu____71429 = FStar_Syntax_Subst.compress t2  in
            uu____71429.FStar_Syntax_Syntax.n  in
          (match uu____71428 with
           | FStar_Syntax_Syntax.Tm_fvar uu____71433 -> false
           | uu____71435 -> is_arity env t2)
      | FStar_Syntax_Syntax.Tm_app uu____71436 ->
          let uu____71453 = FStar_Syntax_Util.head_and_args t1  in
          (match uu____71453 with | (head1,uu____71472) -> is_arity env head1)
      | FStar_Syntax_Syntax.Tm_uinst (head1,uu____71498) ->
          is_arity env head1
      | FStar_Syntax_Syntax.Tm_refine (x,uu____71504) ->
          is_arity env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_abs (uu____71509,body,uu____71511) ->
          is_arity env body
      | FStar_Syntax_Syntax.Tm_let (uu____71536,body) -> is_arity env body
      | FStar_Syntax_Syntax.Tm_match (uu____71556,branches) ->
          (match branches with
           | (uu____71595,uu____71596,e)::uu____71598 -> is_arity env e
           | uu____71645 -> false)
  
let rec (is_type_aux :
  FStar_Extraction_ML_UEnv.uenv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____71677 ->
          let uu____71700 =
            let uu____71702 = FStar_Syntax_Print.tag_of_term t1  in
            FStar_Util.format1 "Impossible: %s" uu____71702  in
          failwith uu____71700
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____71706 =
            let uu____71708 = FStar_Syntax_Print.tag_of_term t1  in
            FStar_Util.format1 "Impossible: %s" uu____71708  in
          failwith uu____71706
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____71713 = FStar_Syntax_Util.unfold_lazy i  in
          is_type_aux env uu____71713
      | FStar_Syntax_Syntax.Tm_constant uu____71714 -> false
      | FStar_Syntax_Syntax.Tm_type uu____71716 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____71718 -> true
      | FStar_Syntax_Syntax.Tm_arrow uu____71726 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.failwith_lid ->
          false
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Extraction_ML_UEnv.is_type_name env fv
      | FStar_Syntax_Syntax.Tm_uvar
          ({ FStar_Syntax_Syntax.ctx_uvar_head = uu____71745;
             FStar_Syntax_Syntax.ctx_uvar_gamma = uu____71746;
             FStar_Syntax_Syntax.ctx_uvar_binders = uu____71747;
             FStar_Syntax_Syntax.ctx_uvar_typ = t2;
             FStar_Syntax_Syntax.ctx_uvar_reason = uu____71749;
             FStar_Syntax_Syntax.ctx_uvar_should_check = uu____71750;
             FStar_Syntax_Syntax.ctx_uvar_range = uu____71751;
             FStar_Syntax_Syntax.ctx_uvar_meta = uu____71752;_},s)
          ->
          let uu____71801 = FStar_Syntax_Subst.subst' s t2  in
          is_arity env uu____71801
      | FStar_Syntax_Syntax.Tm_bvar
          { FStar_Syntax_Syntax.ppname = uu____71802;
            FStar_Syntax_Syntax.index = uu____71803;
            FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_name
          { FStar_Syntax_Syntax.ppname = uu____71808;
            FStar_Syntax_Syntax.index = uu____71809;
            FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____71815,uu____71816) ->
          is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____71858) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____71865) ->
          let uu____71890 = FStar_Syntax_Subst.open_term bs body  in
          (match uu____71890 with
           | (uu____71896,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
          let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
          let uu____71916 =
            let uu____71921 =
              let uu____71922 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____71922]  in
            FStar_Syntax_Subst.open_term uu____71921 body  in
          (match uu____71916 with
           | (uu____71942,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_let ((uu____71944,lbs),body) ->
          let uu____71964 = FStar_Syntax_Subst.open_let_rec lbs body  in
          (match uu____71964 with
           | (uu____71972,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_match (uu____71978,branches) ->
          (match branches with
           | b::uu____72018 ->
               let uu____72063 = FStar_Syntax_Subst.open_branch b  in
               (match uu____72063 with
                | (uu____72065,uu____72066,e) -> is_type_aux env e)
           | uu____72084 -> false)
      | FStar_Syntax_Syntax.Tm_quoted uu____72102 -> false
      | FStar_Syntax_Syntax.Tm_meta (t2,uu____72111) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_app (head1,uu____72117) ->
          is_type_aux env head1
  
let (is_type :
  FStar_Extraction_ML_UEnv.uenv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      FStar_Extraction_ML_UEnv.debug env
        (fun uu____72158  ->
           let uu____72159 = FStar_Syntax_Print.tag_of_term t  in
           let uu____72161 = FStar_Syntax_Print.term_to_string t  in
           FStar_Util.print2 "checking is_type (%s) %s\n" uu____72159
             uu____72161);
      (let b = is_type_aux env t  in
       FStar_Extraction_ML_UEnv.debug env
         (fun uu____72170  ->
            if b
            then
              let uu____72172 = FStar_Syntax_Print.term_to_string t  in
              let uu____72174 = FStar_Syntax_Print.tag_of_term t  in
              FStar_Util.print2 "yes, is_type %s (%s)\n" uu____72172
                uu____72174
            else
              (let uu____72179 = FStar_Syntax_Print.term_to_string t  in
               let uu____72181 = FStar_Syntax_Print.tag_of_term t  in
               FStar_Util.print2 "not a type %s (%s)\n" uu____72179
                 uu____72181));
       b)
  
let is_type_binder :
  'Auu____72191 .
    FStar_Extraction_ML_UEnv.uenv ->
      (FStar_Syntax_Syntax.bv * 'Auu____72191) -> Prims.bool
  =
  fun env  ->
    fun x  ->
      is_arity env (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
  
let (is_constructor : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____72218 =
      let uu____72219 = FStar_Syntax_Subst.compress t  in
      uu____72219.FStar_Syntax_Syntax.n  in
    match uu____72218 with
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____72223;
          FStar_Syntax_Syntax.fv_delta = uu____72224;
          FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
            (FStar_Syntax_Syntax.Data_ctor );_}
        -> true
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____72226;
          FStar_Syntax_Syntax.fv_delta = uu____72227;
          FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
            (FStar_Syntax_Syntax.Record_ctor uu____72228);_}
        -> true
    | uu____72236 -> false
  
let rec (is_fstar_value : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____72245 =
      let uu____72246 = FStar_Syntax_Subst.compress t  in
      uu____72246.FStar_Syntax_Syntax.n  in
    match uu____72245 with
    | FStar_Syntax_Syntax.Tm_constant uu____72250 -> true
    | FStar_Syntax_Syntax.Tm_bvar uu____72252 -> true
    | FStar_Syntax_Syntax.Tm_fvar uu____72254 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____72256 -> true
    | FStar_Syntax_Syntax.Tm_app (head1,args) ->
        let uu____72302 = is_constructor head1  in
        if uu____72302
        then
          FStar_All.pipe_right args
            (FStar_List.for_all
               (fun uu____72324  ->
                  match uu____72324 with
                  | (te,uu____72333) -> is_fstar_value te))
        else false
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____72342) -> is_fstar_value t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____72348,uu____72349) ->
        is_fstar_value t1
    | uu____72390 -> false
  
let rec (is_ml_value : FStar_Extraction_ML_Syntax.mlexpr -> Prims.bool) =
  fun e  ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_Const uu____72400 -> true
    | FStar_Extraction_ML_Syntax.MLE_Var uu____72402 -> true
    | FStar_Extraction_ML_Syntax.MLE_Name uu____72405 -> true
    | FStar_Extraction_ML_Syntax.MLE_Fun uu____72407 -> true
    | FStar_Extraction_ML_Syntax.MLE_CTor (uu____72420,exps) ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Tuple exps ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Record (uu____72429,fields) ->
        FStar_Util.for_all
          (fun uu____72459  ->
             match uu____72459 with | (uu____72466,e1) -> is_ml_value e1)
          fields
    | FStar_Extraction_ML_Syntax.MLE_TApp (h,uu____72471) -> is_ml_value h
    | uu____72476 -> false
  
let (fresh : Prims.string -> Prims.string) =
  let c = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun x  ->
    FStar_Util.incr c;
    (let uu____72527 =
       let uu____72529 = FStar_ST.op_Bang c  in
       FStar_Util.string_of_int uu____72529  in
     Prims.op_Hat x uu____72527)
  
let (normalize_abs : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t0  ->
    let rec aux bs t copt =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_abs (bs',body,copt1) ->
          aux (FStar_List.append bs bs') body copt1
      | uu____72654 ->
          let e' = FStar_Syntax_Util.unascribe t1  in
          let uu____72656 = FStar_Syntax_Util.is_fun e'  in
          if uu____72656
          then aux bs e' copt
          else FStar_Syntax_Util.abs bs e' copt
       in
    aux [] t0 FStar_Pervasives_Native.None
  
let (unit_binder : FStar_Syntax_Syntax.binder) =
  let uu____72670 =
    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
      FStar_Syntax_Syntax.t_unit
     in
  FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____72670 
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
      (let uu____72761 = FStar_List.hd l  in
       match uu____72761 with
       | (p1,w1,e1) ->
           let uu____72796 =
             let uu____72805 = FStar_List.tl l  in FStar_List.hd uu____72805
              in
           (match uu____72796 with
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
                 | uu____72889 -> def)))
  
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
      let uu____72928 = FStar_Extraction_ML_Util.doms_and_cod t  in
      match uu____72928 with
      | (ts,r) ->
          if ts = []
          then e
          else
            (let vs = FStar_List.map (fun uu____72952  -> fresh "a") ts  in
             let vs_ts = FStar_List.zip vs ts  in
             let vs_es =
               let uu____72966 = FStar_List.zip vs ts  in
               FStar_List.map
                 (fun uu____72983  ->
                    match uu____72983 with
                    | (v1,t1) ->
                        FStar_Extraction_ML_Syntax.with_ty t1
                          (FStar_Extraction_ML_Syntax.MLE_Var v1))
                 uu____72966
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
      let uu____73014 = FStar_Extraction_ML_Util.doms_and_cod t  in
      match uu____73014 with
      | (ts,r) ->
          let body r1 =
            let r2 =
              let uu____73034 = FStar_Extraction_ML_Util.udelta_unfold g r1
                 in
              match uu____73034 with
              | FStar_Pervasives_Native.None  -> r1
              | FStar_Pervasives_Native.Some r2 -> r2  in
            match r2 with
            | FStar_Extraction_ML_Syntax.MLTY_Erased  ->
                FStar_Extraction_ML_Syntax.ml_unit
            | FStar_Extraction_ML_Syntax.MLTY_Top  ->
                FStar_Extraction_ML_Syntax.apply_obj_repr
                  FStar_Extraction_ML_Syntax.ml_unit
                  FStar_Extraction_ML_Syntax.MLTY_Erased
            | uu____73038 ->
                FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty r2)
                  (FStar_Extraction_ML_Syntax.MLE_Coerce
                     (FStar_Extraction_ML_Syntax.ml_unit,
                       FStar_Extraction_ML_Syntax.MLTY_Erased, r2))
             in
          if ts = []
          then body r
          else
            (let vs = FStar_List.map (fun uu____73050  -> fresh "a") ts  in
             let vs_ts = FStar_List.zip vs ts  in
             let uu____73061 =
               let uu____73062 =
                 let uu____73074 = body r  in (vs_ts, uu____73074)  in
               FStar_Extraction_ML_Syntax.MLE_Fun uu____73062  in
             FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t)
               uu____73061)
  
let (maybe_eta_expand :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun expect  ->
    fun e  ->
      let uu____73093 =
        (FStar_Options.ml_no_eta_expand_coertions ()) ||
          (let uu____73096 = FStar_Options.codegen ()  in
           uu____73096 = (FStar_Pervasives_Native.Some FStar_Options.Kremlin))
         in
      if uu____73093 then e else eta_expand expect e
  
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
            | uu____73174 ->
                FStar_Extraction_ML_Syntax.MLE_Fun ([binder], body)
             in
          let rec aux e1 ty1 expect1 =
            let coerce_branch uu____73229 =
              match uu____73229 with
              | (pat,w,b) ->
                  let uu____73253 = aux b ty1 expect1  in
                  (pat, w, uu____73253)
               in
            match ((e1.FStar_Extraction_ML_Syntax.expr), ty1, expect1) with
            | (FStar_Extraction_ML_Syntax.MLE_Fun
               (arg::rest,body),FStar_Extraction_ML_Syntax.MLTY_Fun
               (t0,uu____73260,t1),FStar_Extraction_ML_Syntax.MLTY_Fun
               (s0,uu____73263,s1)) ->
                let body1 =
                  match rest with
                  | [] -> body
                  | uu____73295 ->
                      FStar_Extraction_ML_Syntax.with_ty t1
                        (FStar_Extraction_ML_Syntax.MLE_Fun (rest, body))
                   in
                let body2 = aux body1 t1 s1  in
                let uu____73311 = type_leq g s0 t0  in
                if uu____73311
                then
                  FStar_Extraction_ML_Syntax.with_ty expect1
                    (mk_fun arg body2)
                else
                  (let lb =
                     let uu____73317 =
                       let uu____73318 =
                         let uu____73319 =
                           let uu____73326 =
                             FStar_All.pipe_left
                               (FStar_Extraction_ML_Syntax.with_ty s0)
                               (FStar_Extraction_ML_Syntax.MLE_Var
                                  (FStar_Pervasives_Native.fst arg))
                              in
                           (uu____73326, s0, t0)  in
                         FStar_Extraction_ML_Syntax.MLE_Coerce uu____73319
                          in
                       FStar_Extraction_ML_Syntax.with_ty t0 uu____73318  in
                     {
                       FStar_Extraction_ML_Syntax.mllb_name =
                         (FStar_Pervasives_Native.fst arg);
                       FStar_Extraction_ML_Syntax.mllb_tysc =
                         (FStar_Pervasives_Native.Some ([], t0));
                       FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                       FStar_Extraction_ML_Syntax.mllb_def = uu____73317;
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
               (lbs,body),uu____73345,uu____73346) ->
                let uu____73359 =
                  let uu____73360 =
                    let uu____73371 = aux body ty1 expect1  in
                    (lbs, uu____73371)  in
                  FStar_Extraction_ML_Syntax.MLE_Let uu____73360  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____73359
            | (FStar_Extraction_ML_Syntax.MLE_Match
               (s,branches),uu____73380,uu____73381) ->
                let uu____73402 =
                  let uu____73403 =
                    let uu____73418 = FStar_List.map coerce_branch branches
                       in
                    (s, uu____73418)  in
                  FStar_Extraction_ML_Syntax.MLE_Match uu____73403  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____73402
            | (FStar_Extraction_ML_Syntax.MLE_If
               (s,b1,b2_opt),uu____73458,uu____73459) ->
                let uu____73464 =
                  let uu____73465 =
                    let uu____73474 = aux b1 ty1 expect1  in
                    let uu____73475 =
                      FStar_Util.map_opt b2_opt
                        (fun b2  -> aux b2 ty1 expect1)
                       in
                    (s, uu____73474, uu____73475)  in
                  FStar_Extraction_ML_Syntax.MLE_If uu____73465  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____73464
            | (FStar_Extraction_ML_Syntax.MLE_Seq es,uu____73483,uu____73484)
                ->
                let uu____73487 = FStar_Util.prefix es  in
                (match uu____73487 with
                 | (prefix1,last1) ->
                     let uu____73500 =
                       let uu____73501 =
                         let uu____73504 =
                           let uu____73507 = aux last1 ty1 expect1  in
                           [uu____73507]  in
                         FStar_List.append prefix1 uu____73504  in
                       FStar_Extraction_ML_Syntax.MLE_Seq uu____73501  in
                     FStar_All.pipe_left
                       (FStar_Extraction_ML_Syntax.with_ty expect1)
                       uu____73500)
            | (FStar_Extraction_ML_Syntax.MLE_Try
               (s,branches),uu____73510,uu____73511) ->
                let uu____73532 =
                  let uu____73533 =
                    let uu____73548 = FStar_List.map coerce_branch branches
                       in
                    (s, uu____73548)  in
                  FStar_Extraction_ML_Syntax.MLE_Try uu____73533  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____73532
            | uu____73585 ->
                FStar_Extraction_ML_Syntax.with_ty expect1
                  (FStar_Extraction_ML_Syntax.MLE_Coerce (e1, ty1, expect1))
             in
          aux e ty expect
  
let maybe_coerce :
  'Auu____73605 .
    'Auu____73605 ->
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
            let uu____73632 =
              type_leq_c g (FStar_Pervasives_Native.Some e) ty1 expect  in
            match uu____73632 with
            | (true ,FStar_Pervasives_Native.Some e') -> e'
            | uu____73645 ->
                (match ty1 with
                 | FStar_Extraction_ML_Syntax.MLTY_Erased  ->
                     default_value_for_ty g expect
                 | uu____73653 ->
                     let uu____73654 =
                       let uu____73656 =
                         FStar_Extraction_ML_Util.erase_effect_annotations
                           ty1
                          in
                       let uu____73657 =
                         FStar_Extraction_ML_Util.erase_effect_annotations
                           expect
                          in
                       type_leq g uu____73656 uu____73657  in
                     if uu____73654
                     then
                       (FStar_Extraction_ML_UEnv.debug g
                          (fun uu____73663  ->
                             let uu____73664 =
                               FStar_Extraction_ML_Code.string_of_mlexpr
                                 g.FStar_Extraction_ML_UEnv.currentModule e
                                in
                             let uu____73666 =
                               FStar_Extraction_ML_Code.string_of_mlty
                                 g.FStar_Extraction_ML_UEnv.currentModule ty1
                                in
                             FStar_Util.print2
                               "\n Effect mismatch on type of %s : %s\n"
                               uu____73664 uu____73666);
                        e)
                     else
                       (FStar_Extraction_ML_UEnv.debug g
                          (fun uu____73676  ->
                             let uu____73677 =
                               FStar_Extraction_ML_Code.string_of_mlexpr
                                 g.FStar_Extraction_ML_UEnv.currentModule e
                                in
                             let uu____73679 =
                               FStar_Extraction_ML_Code.string_of_mlty
                                 g.FStar_Extraction_ML_UEnv.currentModule ty1
                                in
                             let uu____73681 =
                               FStar_Extraction_ML_Code.string_of_mlty
                                 g.FStar_Extraction_ML_UEnv.currentModule
                                 expect
                                in
                             FStar_Util.print3
                               "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n"
                               uu____73677 uu____73679 uu____73681);
                        (let uu____73684 = apply_coercion g e ty1 expect  in
                         maybe_eta_expand expect uu____73684)))
  
let (bv_as_mlty :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun bv  ->
      let uu____73696 = FStar_Extraction_ML_UEnv.lookup_bv g bv  in
      match uu____73696 with
      | FStar_Util.Inl ty_b -> ty_b.FStar_Extraction_ML_UEnv.ty_b_ty
      | uu____73698 -> FStar_Extraction_ML_Syntax.MLTY_Top
  
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
    | FStar_Syntax_Syntax.Total uu____73716 -> c
    | FStar_Syntax_Syntax.GTotal uu____73725 -> c
    | FStar_Syntax_Syntax.Comp ct ->
        let effect_args =
          FStar_List.map
            (fun uu____73761  ->
               match uu____73761 with
               | (uu____73776,aq) -> (FStar_Syntax_Syntax.t_unit, aq))
            ct.FStar_Syntax_Syntax.effect_args
           in
        let ct1 =
          let uu___1129_73789 = ct  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___1129_73789.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___1129_73789.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ =
              (uu___1129_73789.FStar_Syntax_Syntax.result_typ);
            FStar_Syntax_Syntax.effect_args = effect_args;
            FStar_Syntax_Syntax.flags =
              (uu___1129_73789.FStar_Syntax_Syntax.flags)
          }  in
        let c1 =
          let uu___1132_73793 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
            FStar_Syntax_Syntax.pos =
              (uu___1132_73793.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___1132_73793.FStar_Syntax_Syntax.vars)
          }  in
        c1
  
let rec (translate_term_to_mlty :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun t0  ->
      let arg_as_mlty g1 uu____73842 =
        match uu____73842 with
        | (a,uu____73850) ->
            let uu____73855 = is_type g1 a  in
            if uu____73855
            then translate_term_to_mlty g1 a
            else FStar_Extraction_ML_UEnv.erasedContent
         in
      let fv_app_as_mlty g1 fv args =
        let uu____73876 =
          let uu____73878 = FStar_Extraction_ML_UEnv.is_fv_type g1 fv  in
          Prims.op_Negation uu____73878  in
        if uu____73876
        then FStar_Extraction_ML_Syntax.MLTY_Top
        else
          (let uu____73883 =
             let uu____73898 =
               FStar_TypeChecker_Env.lookup_lid
                 g1.FStar_Extraction_ML_UEnv.env_tcenv
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             match uu____73898 with
             | ((uu____73921,fvty),uu____73923) ->
                 let fvty1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Env.UnfoldUntil
                        FStar_Syntax_Syntax.delta_constant]
                     g1.FStar_Extraction_ML_UEnv.env_tcenv fvty
                    in
                 FStar_Syntax_Util.arrow_formals fvty1
              in
           match uu____73883 with
           | (formals,uu____73930) ->
               let mlargs = FStar_List.map (arg_as_mlty g1) args  in
               let mlargs1 =
                 let n_args = FStar_List.length args  in
                 if (FStar_List.length formals) > n_args
                 then
                   let uu____73987 = FStar_Util.first_N n_args formals  in
                   match uu____73987 with
                   | (uu____74020,rest) ->
                       let uu____74054 =
                         FStar_List.map
                           (fun uu____74064  ->
                              FStar_Extraction_ML_UEnv.erasedContent) rest
                          in
                       FStar_List.append mlargs uu____74054
                 else mlargs  in
               let nm =
                 let uu____74074 =
                   FStar_Extraction_ML_UEnv.maybe_mangle_type_projector g1 fv
                    in
                 match uu____74074 with
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
        | FStar_Syntax_Syntax.Tm_type uu____74092 ->
            FStar_Extraction_ML_Syntax.MLTY_Erased
        | FStar_Syntax_Syntax.Tm_bvar uu____74093 ->
            let uu____74094 =
              let uu____74096 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____74096
               in
            failwith uu____74094
        | FStar_Syntax_Syntax.Tm_delayed uu____74099 ->
            let uu____74122 =
              let uu____74124 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____74124
               in
            failwith uu____74122
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____74127 =
              let uu____74129 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____74129
               in
            failwith uu____74127
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____74133 = FStar_Syntax_Util.unfold_lazy i  in
            translate_term_to_mlty env uu____74133
        | FStar_Syntax_Syntax.Tm_constant uu____74134 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_quoted uu____74135 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_uvar uu____74142 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_meta (t2,uu____74156) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____74161;
               FStar_Syntax_Syntax.index = uu____74162;
               FStar_Syntax_Syntax.sort = t2;_},uu____74164)
            -> translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_uinst (t2,uu____74173) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____74179,uu____74180) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
        | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv []
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let uu____74253 = FStar_Syntax_Subst.open_comp bs c  in
            (match uu____74253 with
             | (bs1,c1) ->
                 let uu____74260 = binders_as_ml_binders env bs1  in
                 (match uu____74260 with
                  | (mlbs,env1) ->
                      let t_ret =
                        let eff =
                          FStar_TypeChecker_Env.norm_eff_name
                            env1.FStar_Extraction_ML_UEnv.env_tcenv
                            (FStar_Syntax_Util.comp_effect_name c1)
                           in
                        let c2 = comp_no_args c1  in
                        let uu____74293 =
                          let uu____74300 =
                            FStar_TypeChecker_Env.effect_decl_opt
                              env1.FStar_Extraction_ML_UEnv.env_tcenv eff
                             in
                          FStar_Util.must uu____74300  in
                        match uu____74293 with
                        | (ed,qualifiers) ->
                            let uu____74321 =
                              FStar_TypeChecker_Env.is_reifiable_effect
                                g.FStar_Extraction_ML_UEnv.env_tcenv
                                ed.FStar_Syntax_Syntax.mname
                               in
                            if uu____74321
                            then
                              let t2 =
                                FStar_TypeChecker_Env.reify_comp
                                  env1.FStar_Extraction_ML_UEnv.env_tcenv c2
                                  FStar_Syntax_Syntax.U_unknown
                                 in
                              (FStar_Extraction_ML_UEnv.debug env1
                                 (fun uu____74329  ->
                                    let uu____74330 =
                                      FStar_Syntax_Print.comp_to_string c2
                                       in
                                    let uu____74332 =
                                      FStar_Syntax_Print.term_to_string t2
                                       in
                                    FStar_Util.print2
                                      "Translating comp type %s as %s\n"
                                      uu____74330 uu____74332);
                               (let res = translate_term_to_mlty env1 t2  in
                                FStar_Extraction_ML_UEnv.debug env1
                                  (fun uu____74341  ->
                                     let uu____74342 =
                                       FStar_Syntax_Print.comp_to_string c2
                                        in
                                     let uu____74344 =
                                       FStar_Syntax_Print.term_to_string t2
                                        in
                                     let uu____74346 =
                                       FStar_Extraction_ML_Code.string_of_mlty
                                         env1.FStar_Extraction_ML_UEnv.currentModule
                                         res
                                        in
                                     FStar_Util.print3
                                       "Translated comp type %s as %s ... to %s\n"
                                       uu____74342 uu____74344 uu____74346);
                                res))
                            else
                              translate_term_to_mlty env1
                                (FStar_Syntax_Util.comp_result c2)
                         in
                      let erase =
                        effect_as_etag env1
                          (FStar_Syntax_Util.comp_effect_name c1)
                         in
                      let uu____74352 =
                        FStar_List.fold_right
                          (fun uu____74372  ->
                             fun uu____74373  ->
                               match (uu____74372, uu____74373) with
                               | ((uu____74396,t2),(tag,t')) ->
                                   (FStar_Extraction_ML_Syntax.E_PURE,
                                     (FStar_Extraction_ML_Syntax.MLTY_Fun
                                        (t2, tag, t')))) mlbs (erase, t_ret)
                         in
                      (match uu____74352 with | (uu____74411,t2) -> t2)))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let res =
              let uu____74440 =
                let uu____74441 = FStar_Syntax_Util.un_uinst head1  in
                uu____74441.FStar_Syntax_Syntax.n  in
              match uu____74440 with
              | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv args
              | FStar_Syntax_Syntax.Tm_app (head2,args') ->
                  let uu____74472 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_app
                         (head2, (FStar_List.append args' args)))
                      FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                     in
                  translate_term_to_mlty env uu____74472
              | uu____74493 -> FStar_Extraction_ML_UEnv.unknownType  in
            res
        | FStar_Syntax_Syntax.Tm_abs (bs,ty,uu____74496) ->
            let uu____74521 = FStar_Syntax_Subst.open_term bs ty  in
            (match uu____74521 with
             | (bs1,ty1) ->
                 let uu____74528 = binders_as_ml_binders env bs1  in
                 (match uu____74528 with
                  | (bts,env1) -> translate_term_to_mlty env1 ty1))
        | FStar_Syntax_Syntax.Tm_let uu____74556 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_match uu____74570 ->
            FStar_Extraction_ML_UEnv.unknownType
         in
      let rec is_top_ty t =
        match t with
        | FStar_Extraction_ML_Syntax.MLTY_Top  -> true
        | FStar_Extraction_ML_Syntax.MLTY_Named uu____74602 ->
            let uu____74609 = FStar_Extraction_ML_Util.udelta_unfold g t  in
            (match uu____74609 with
             | FStar_Pervasives_Native.None  -> false
             | FStar_Pervasives_Native.Some t1 -> is_top_ty t1)
        | uu____74615 -> false  in
      let uu____74617 =
        FStar_TypeChecker_Util.must_erase_for_extraction
          g.FStar_Extraction_ML_UEnv.env_tcenv t0
         in
      if uu____74617
      then FStar_Extraction_ML_Syntax.MLTY_Erased
      else
        (let mlt = aux g t0  in
         let uu____74623 = is_top_ty mlt  in
         if uu____74623
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
      let uu____74642 =
        FStar_All.pipe_right bs
          (FStar_List.fold_left
             (fun uu____74698  ->
                fun b  ->
                  match uu____74698 with
                  | (ml_bs,env) ->
                      let uu____74744 = is_type_binder g b  in
                      if uu____74744
                      then
                        let b1 = FStar_Pervasives_Native.fst b  in
                        let env1 =
                          FStar_Extraction_ML_UEnv.extend_ty env b1
                            (FStar_Pervasives_Native.Some
                               FStar_Extraction_ML_Syntax.MLTY_Top)
                           in
                        let ml_b =
                          let uu____74770 =
                            FStar_Extraction_ML_UEnv.bv_as_ml_termvar b1  in
                          (uu____74770,
                            FStar_Extraction_ML_Syntax.ml_unit_ty)
                           in
                        ((ml_b :: ml_bs), env1)
                      else
                        (let b1 = FStar_Pervasives_Native.fst b  in
                         let t =
                           translate_term_to_mlty env
                             b1.FStar_Syntax_Syntax.sort
                            in
                         let uu____74791 =
                           FStar_Extraction_ML_UEnv.extend_bv env b1 
                             ([], t) false false false
                            in
                         match uu____74791 with
                         | (env1,b2,uu____74816) ->
                             let ml_b =
                               let uu____74825 =
                                 FStar_Extraction_ML_UEnv.removeTick b2  in
                               (uu____74825, t)  in
                             ((ml_b :: ml_bs), env1))) ([], g))
         in
      match uu____74642 with | (ml_bs,env) -> ((FStar_List.rev ml_bs), env)

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
      | (FStar_Extraction_ML_Syntax.MLE_Seq es1,uu____74921) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (FStar_List.append es1 [e2])
      | (uu____74924,FStar_Extraction_ML_Syntax.MLE_Seq es2) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (e1 :: es2)
      | uu____74928 -> FStar_Extraction_ML_Syntax.MLE_Seq [e1; e2]
  
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
                    | uu____74962 when
                        (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
                          =
                          FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr
                        -> body.FStar_Extraction_ML_Syntax.expr
                    | uu____74963 ->
                        mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def
                          body)
             | uu____74964 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body))
        | uu____74973 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body)
  
let (resugar_pat :
  FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option ->
    FStar_Extraction_ML_Syntax.mlpattern ->
      FStar_Extraction_ML_Syntax.mlpattern)
  =
  fun q  ->
    fun p  ->
      match p with
      | FStar_Extraction_ML_Syntax.MLP_CTor (d,pats) ->
          let uu____75001 = FStar_Extraction_ML_Util.is_xtuple d  in
          (match uu____75001 with
           | FStar_Pervasives_Native.Some n1 ->
               FStar_Extraction_ML_Syntax.MLP_Tuple pats
           | uu____75008 ->
               (match q with
                | FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Record_ctor (ty,fns)) ->
                    let path =
                      FStar_List.map FStar_Ident.text_of_id ty.FStar_Ident.ns
                       in
                    let fs = record_fields fns pats  in
                    FStar_Extraction_ML_Syntax.MLP_Record (path, fs)
                | uu____75041 -> p))
      | uu____75044 -> p
  
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
                       (fun uu____75146  ->
                          let uu____75147 =
                            FStar_Extraction_ML_Code.string_of_mlty
                              g.FStar_Extraction_ML_UEnv.currentModule t'
                             in
                          let uu____75149 =
                            FStar_Extraction_ML_Code.string_of_mlty
                              g.FStar_Extraction_ML_UEnv.currentModule t
                             in
                          FStar_Util.print2
                            "Expected pattern type %s; got pattern type %s\n"
                            uu____75147 uu____75149)
                   else ();
                   ok)
               in
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int
                (c,swopt)) when
                let uu____75185 = FStar_Options.codegen ()  in
                uu____75185 <>
                  (FStar_Pervasives_Native.Some FStar_Options.Kremlin)
                ->
                let uu____75190 =
                  match swopt with
                  | FStar_Pervasives_Native.None  ->
                      let uu____75203 =
                        let uu____75204 =
                          let uu____75205 =
                            FStar_Extraction_ML_Util.mlconst_of_const
                              p.FStar_Syntax_Syntax.p
                              (FStar_Const.Const_int
                                 (c, FStar_Pervasives_Native.None))
                             in
                          FStar_Extraction_ML_Syntax.MLE_Const uu____75205
                           in
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.ml_int_ty)
                          uu____75204
                         in
                      (uu____75203, FStar_Extraction_ML_Syntax.ml_int_ty)
                  | FStar_Pervasives_Native.Some sw ->
                      let source_term =
                        FStar_ToSyntax_ToSyntax.desugar_machine_integer
                          (g.FStar_Extraction_ML_UEnv.env_tcenv).FStar_TypeChecker_Env.dsenv
                          c sw FStar_Range.dummyRange
                         in
                      let uu____75227 = term_as_mlexpr g source_term  in
                      (match uu____75227 with
                       | (mlterm,uu____75239,mlty) -> (mlterm, mlty))
                   in
                (match uu____75190 with
                 | (mlc,ml_ty) ->
                     let x = FStar_Extraction_ML_Syntax.gensym ()  in
                     let when_clause =
                       let uu____75261 =
                         let uu____75262 =
                           let uu____75269 =
                             let uu____75272 =
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty ml_ty)
                                 (FStar_Extraction_ML_Syntax.MLE_Var x)
                                in
                             [uu____75272; mlc]  in
                           (FStar_Extraction_ML_Util.prims_op_equality,
                             uu____75269)
                            in
                         FStar_Extraction_ML_Syntax.MLE_App uu____75262  in
                       FStar_All.pipe_left
                         (FStar_Extraction_ML_Syntax.with_ty
                            FStar_Extraction_ML_Syntax.ml_bool_ty)
                         uu____75261
                        in
                     let uu____75275 = ok ml_ty  in
                     (g,
                       (FStar_Pervasives_Native.Some
                          ((FStar_Extraction_ML_Syntax.MLP_Var x),
                            [when_clause])), uu____75275))
            | FStar_Syntax_Syntax.Pat_constant s ->
                let t =
                  FStar_TypeChecker_TcTerm.tc_constant
                    g.FStar_Extraction_ML_UEnv.env_tcenv
                    FStar_Range.dummyRange s
                   in
                let mlty = term_as_mlty g t  in
                let uu____75297 =
                  let uu____75306 =
                    let uu____75313 =
                      let uu____75314 =
                        FStar_Extraction_ML_Util.mlconst_of_const
                          p.FStar_Syntax_Syntax.p s
                         in
                      FStar_Extraction_ML_Syntax.MLP_Const uu____75314  in
                    (uu____75313, [])  in
                  FStar_Pervasives_Native.Some uu____75306  in
                let uu____75323 = ok mlty  in (g, uu____75297, uu____75323)
            | FStar_Syntax_Syntax.Pat_var x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort  in
                let uu____75336 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp
                   in
                (match uu____75336 with
                 | (g1,x1,uu____75364) ->
                     let uu____75367 = ok mlty  in
                     (g1,
                       (if imp
                        then FStar_Pervasives_Native.None
                        else
                          FStar_Pervasives_Native.Some
                            ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                       uu____75367))
            | FStar_Syntax_Syntax.Pat_wild x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort  in
                let uu____75405 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp
                   in
                (match uu____75405 with
                 | (g1,x1,uu____75433) ->
                     let uu____75436 = ok mlty  in
                     (g1,
                       (if imp
                        then FStar_Pervasives_Native.None
                        else
                          FStar_Pervasives_Native.Some
                            ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                       uu____75436))
            | FStar_Syntax_Syntax.Pat_dot_term uu____75472 ->
                (g, FStar_Pervasives_Native.None, true)
            | FStar_Syntax_Syntax.Pat_cons (f,pats) ->
                let uu____75515 =
                  let uu____75524 = FStar_Extraction_ML_UEnv.lookup_fv g f
                     in
                  match uu____75524 with
                  | { FStar_Extraction_ML_UEnv.exp_b_name = uu____75533;
                      FStar_Extraction_ML_UEnv.exp_b_expr =
                        {
                          FStar_Extraction_ML_Syntax.expr =
                            FStar_Extraction_ML_Syntax.MLE_Name n1;
                          FStar_Extraction_ML_Syntax.mlty = uu____75535;
                          FStar_Extraction_ML_Syntax.loc = uu____75536;_};
                      FStar_Extraction_ML_UEnv.exp_b_tscheme = ttys;
                      FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____75538;_}
                      -> (n1, ttys)
                  | uu____75545 -> failwith "Expected a constructor"  in
                (match uu____75515 with
                 | (d,tys) ->
                     let nTyVars =
                       FStar_List.length (FStar_Pervasives_Native.fst tys)
                        in
                     let uu____75582 = FStar_Util.first_N nTyVars pats  in
                     (match uu____75582 with
                      | (tysVarPats,restPats) ->
                          let f_ty_opt =
                            try
                              (fun uu___1428_75690  ->
                                 match () with
                                 | () ->
                                     let mlty_args =
                                       FStar_All.pipe_right tysVarPats
                                         (FStar_List.map
                                            (fun uu____75721  ->
                                               match uu____75721 with
                                               | (p1,uu____75728) ->
                                                   (match p1.FStar_Syntax_Syntax.v
                                                    with
                                                    | FStar_Syntax_Syntax.Pat_dot_term
                                                        (uu____75731,t) ->
                                                        term_as_mlty g t
                                                    | uu____75737 ->
                                                        (FStar_Extraction_ML_UEnv.debug
                                                           g
                                                           (fun uu____75741 
                                                              ->
                                                              let uu____75742
                                                                =
                                                                FStar_Syntax_Print.pat_to_string
                                                                  p1
                                                                 in
                                                              FStar_Util.print1
                                                                "Pattern %s is not extractable"
                                                                uu____75742);
                                                         FStar_Exn.raise
                                                           Un_extractable))))
                                        in
                                     let f_ty =
                                       FStar_Extraction_ML_Util.subst tys
                                         mlty_args
                                        in
                                     let uu____75746 =
                                       FStar_Extraction_ML_Util.uncurry_mlty_fun
                                         f_ty
                                        in
                                     FStar_Pervasives_Native.Some uu____75746)
                                ()
                            with
                            | Un_extractable  -> FStar_Pervasives_Native.None
                             in
                          let uu____75775 =
                            FStar_Util.fold_map
                              (fun g1  ->
                                 fun uu____75812  ->
                                   match uu____75812 with
                                   | (p1,imp1) ->
                                       let uu____75834 =
                                         extract_one_pat true g1 p1
                                           FStar_Pervasives_Native.None
                                           term_as_mlexpr
                                          in
                                       (match uu____75834 with
                                        | (g2,p2,uu____75865) -> (g2, p2))) g
                              tysVarPats
                             in
                          (match uu____75775 with
                           | (g1,tyMLPats) ->
                               let uu____75929 =
                                 FStar_Util.fold_map
                                   (fun uu____75994  ->
                                      fun uu____75995  ->
                                        match (uu____75994, uu____75995) with
                                        | ((g2,f_ty_opt1),(p1,imp1)) ->
                                            let uu____76093 =
                                              match f_ty_opt1 with
                                              | FStar_Pervasives_Native.Some
                                                  (hd1::rest,res) ->
                                                  ((FStar_Pervasives_Native.Some
                                                      (rest, res)),
                                                    (FStar_Pervasives_Native.Some
                                                       hd1))
                                              | uu____76153 ->
                                                  (FStar_Pervasives_Native.None,
                                                    FStar_Pervasives_Native.None)
                                               in
                                            (match uu____76093 with
                                             | (f_ty_opt2,expected_ty) ->
                                                 let uu____76224 =
                                                   extract_one_pat false g2
                                                     p1 expected_ty
                                                     term_as_mlexpr
                                                    in
                                                 (match uu____76224 with
                                                  | (g3,p2,uu____76267) ->
                                                      ((g3, f_ty_opt2), p2))))
                                   (g1, f_ty_opt) restPats
                                  in
                               (match uu____75929 with
                                | ((g2,f_ty_opt1),restMLPats) ->
                                    let uu____76388 =
                                      let uu____76399 =
                                        FStar_All.pipe_right
                                          (FStar_List.append tyMLPats
                                             restMLPats)
                                          (FStar_List.collect
                                             (fun uu___618_76450  ->
                                                match uu___618_76450 with
                                                | FStar_Pervasives_Native.Some
                                                    x -> [x]
                                                | uu____76492 -> []))
                                         in
                                      FStar_All.pipe_right uu____76399
                                        FStar_List.split
                                       in
                                    (match uu____76388 with
                                     | (mlPats,when_clauses) ->
                                         let pat_ty_compat =
                                           match f_ty_opt1 with
                                           | FStar_Pervasives_Native.Some
                                               ([],t) -> ok t
                                           | uu____76568 -> false  in
                                         let uu____76578 =
                                           let uu____76587 =
                                             let uu____76594 =
                                               resugar_pat
                                                 f.FStar_Syntax_Syntax.fv_qual
                                                 (FStar_Extraction_ML_Syntax.MLP_CTor
                                                    (d, mlPats))
                                                in
                                             let uu____76597 =
                                               FStar_All.pipe_right
                                                 when_clauses
                                                 FStar_List.flatten
                                                in
                                             (uu____76594, uu____76597)  in
                                           FStar_Pervasives_Native.Some
                                             uu____76587
                                            in
                                         (g2, uu____76578, pat_ty_compat))))))
  
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
            let uu____76729 =
              extract_one_pat false g1 p1 expected_t1 term_as_mlexpr  in
            match uu____76729 with
            | (g2,FStar_Pervasives_Native.Some (x,v1),b) -> (g2, (x, v1), b)
            | uu____76792 ->
                failwith "Impossible: Unable to translate pattern"
             in
          let mk_when_clause whens =
            match whens with
            | [] -> FStar_Pervasives_Native.None
            | hd1::tl1 ->
                let uu____76840 =
                  FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd1
                    tl1
                   in
                FStar_Pervasives_Native.Some uu____76840
             in
          let uu____76841 =
            extract_one_pat1 g p (FStar_Pervasives_Native.Some expected_t)
             in
          match uu____76841 with
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
            | FStar_Extraction_ML_Syntax.MLTY_Fun (t0,uu____77001,t1) ->
                let x = FStar_Extraction_ML_Syntax.gensym ()  in
                let uu____77005 =
                  let uu____77017 =
                    let uu____77027 =
                      FStar_All.pipe_left
                        (FStar_Extraction_ML_Syntax.with_ty t0)
                        (FStar_Extraction_ML_Syntax.MLE_Var x)
                       in
                    ((x, t0), uu____77027)  in
                  uu____77017 :: more_args  in
                eta_args uu____77005 t1
            | FStar_Extraction_ML_Syntax.MLTY_Named (uu____77043,uu____77044)
                -> ((FStar_List.rev more_args), t)
            | uu____77069 ->
                let uu____77070 =
                  let uu____77072 =
                    FStar_Extraction_ML_Code.string_of_mlexpr
                      g.FStar_Extraction_ML_UEnv.currentModule mlAppExpr
                     in
                  let uu____77074 =
                    FStar_Extraction_ML_Code.string_of_mlty
                      g.FStar_Extraction_ML_UEnv.currentModule t
                     in
                  FStar_Util.format2
                    "Impossible: Head type is not an arrow: (%s : %s)"
                    uu____77072 uu____77074
                   in
                failwith uu____77070
             in
          let as_record qual1 e =
            match ((e.FStar_Extraction_ML_Syntax.expr), qual1) with
            | (FStar_Extraction_ML_Syntax.MLE_CTor
               (uu____77109,args),FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Record_ctor (tyname,fields))) ->
                let path =
                  FStar_List.map FStar_Ident.text_of_id tyname.FStar_Ident.ns
                   in
                let fields1 = record_fields fields args  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     e.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_Record (path, fields1))
            | uu____77146 -> e  in
          let resugar_and_maybe_eta qual1 e =
            let uu____77168 = eta_args [] residualType  in
            match uu____77168 with
            | (eargs,tres) ->
                (match eargs with
                 | [] ->
                     let uu____77226 = as_record qual1 e  in
                     FStar_Extraction_ML_Util.resugar_exp uu____77226
                 | uu____77227 ->
                     let uu____77239 = FStar_List.unzip eargs  in
                     (match uu____77239 with
                      | (binders,eargs1) ->
                          (match e.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_CTor (head1,args)
                               ->
                               let body =
                                 let uu____77285 =
                                   let uu____77286 =
                                     FStar_All.pipe_left
                                       (FStar_Extraction_ML_Syntax.with_ty
                                          tres)
                                       (FStar_Extraction_ML_Syntax.MLE_CTor
                                          (head1,
                                            (FStar_List.append args eargs1)))
                                      in
                                   FStar_All.pipe_left (as_record qual1)
                                     uu____77286
                                    in
                                 FStar_All.pipe_left
                                   FStar_Extraction_ML_Util.resugar_exp
                                   uu____77285
                                  in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    e.FStar_Extraction_ML_Syntax.mlty)
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    (binders, body))
                           | uu____77296 ->
                               failwith "Impossible: Not a constructor")))
             in
          match ((mlAppExpr.FStar_Extraction_ML_Syntax.expr), qual) with
          | (uu____77300,FStar_Pervasives_Native.None ) -> mlAppExpr
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____77304;
                FStar_Extraction_ML_Syntax.loc = uu____77305;_},mle::args),FStar_Pervasives_Native.Some
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
                | uu____77328 ->
                    let uu____77331 =
                      let uu____77338 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj
                         in
                      (uu____77338, args)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____77331
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
                     FStar_Extraction_ML_Syntax.mlty = uu____77342;
                     FStar_Extraction_ML_Syntax.loc = uu____77343;_},uu____77344);
                FStar_Extraction_ML_Syntax.mlty = uu____77345;
                FStar_Extraction_ML_Syntax.loc = uu____77346;_},mle::args),FStar_Pervasives_Native.Some
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
                | uu____77373 ->
                    let uu____77376 =
                      let uu____77383 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj
                         in
                      (uu____77383, args)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____77376
                 in
              FStar_Extraction_ML_Syntax.with_ty
                mlAppExpr.FStar_Extraction_ML_Syntax.mlty e
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____77387;
                FStar_Extraction_ML_Syntax.loc = uu____77388;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____77396 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____77396
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____77400;
                FStar_Extraction_ML_Syntax.loc = uu____77401;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____77403)) ->
              let uu____77416 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____77416
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____77420;
                     FStar_Extraction_ML_Syntax.loc = uu____77421;_},uu____77422);
                FStar_Extraction_ML_Syntax.mlty = uu____77423;
                FStar_Extraction_ML_Syntax.loc = uu____77424;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____77436 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____77436
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____77440;
                     FStar_Extraction_ML_Syntax.loc = uu____77441;_},uu____77442);
                FStar_Extraction_ML_Syntax.mlty = uu____77443;
                FStar_Extraction_ML_Syntax.loc = uu____77444;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____77446)) ->
              let uu____77463 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____77463
          | (FStar_Extraction_ML_Syntax.MLE_Name
             mlp,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor
             )) ->
              let uu____77469 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____77469
          | (FStar_Extraction_ML_Syntax.MLE_Name
             mlp,FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____77473)) ->
              let uu____77482 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____77482
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____77486;
                FStar_Extraction_ML_Syntax.loc = uu____77487;_},uu____77488),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____77495 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____77495
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____77499;
                FStar_Extraction_ML_Syntax.loc = uu____77500;_},uu____77501),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____77502)) ->
              let uu____77515 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____77515
          | uu____77518 -> mlAppExpr
  
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
        | uu____77549 -> (ml_e, tag)
  
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
      let maybe_generalize uu____77610 =
        match uu____77610 with
        | { FStar_Syntax_Syntax.lbname = lbname_;
            FStar_Syntax_Syntax.lbunivs = uu____77631;
            FStar_Syntax_Syntax.lbtyp = lbtyp;
            FStar_Syntax_Syntax.lbeff = lbeff;
            FStar_Syntax_Syntax.lbdef = lbdef;
            FStar_Syntax_Syntax.lbattrs = uu____77635;
            FStar_Syntax_Syntax.lbpos = uu____77636;_} ->
            let f_e = effect_as_etag g lbeff  in
            let lbtyp1 = FStar_Syntax_Subst.compress lbtyp  in
            let no_gen uu____77717 =
              let expected_t = term_as_mlty g lbtyp1  in
              (lbname_, f_e, (lbtyp1, ([], ([], expected_t))), false, lbdef)
               in
            let uu____77794 =
              FStar_TypeChecker_Util.must_erase_for_extraction
                g.FStar_Extraction_ML_UEnv.env_tcenv lbtyp1
               in
            if uu____77794
            then
              (lbname_, f_e,
                (lbtyp1, ([], ([], FStar_Extraction_ML_Syntax.MLTY_Erased))),
                false, lbdef)
            else
              (match lbtyp1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                   let uu____77880 = FStar_List.hd bs  in
                   FStar_All.pipe_right uu____77880 (is_type_binder g) ->
                   let uu____77902 = FStar_Syntax_Subst.open_comp bs c  in
                   (match uu____77902 with
                    | (bs1,c1) ->
                        let uu____77928 =
                          let uu____77941 =
                            FStar_Util.prefix_until
                              (fun x  ->
                                 let uu____77987 = is_type_binder g x  in
                                 Prims.op_Negation uu____77987) bs1
                             in
                          match uu____77941 with
                          | FStar_Pervasives_Native.None  ->
                              (bs1, (FStar_Syntax_Util.comp_result c1))
                          | FStar_Pervasives_Native.Some (bs2,b,rest) ->
                              let uu____78114 =
                                FStar_Syntax_Util.arrow (b :: rest) c1  in
                              (bs2, uu____78114)
                           in
                        (match uu____77928 with
                         | (tbinders,tbody) ->
                             let n_tbinders = FStar_List.length tbinders  in
                             let lbdef1 =
                               let uu____78176 = normalize_abs lbdef  in
                               FStar_All.pipe_right uu____78176
                                 FStar_Syntax_Util.unmeta
                                in
                             (match lbdef1.FStar_Syntax_Syntax.n with
                              | FStar_Syntax_Syntax.Tm_abs (bs2,body,copt) ->
                                  let uu____78225 =
                                    FStar_Syntax_Subst.open_term bs2 body  in
                                  (match uu____78225 with
                                   | (bs3,body1) ->
                                       if
                                         n_tbinders <=
                                           (FStar_List.length bs3)
                                       then
                                         let uu____78283 =
                                           FStar_Util.first_N n_tbinders bs3
                                            in
                                         (match uu____78283 with
                                          | (targs,rest_args) ->
                                              let expected_source_ty =
                                                let s =
                                                  FStar_List.map2
                                                    (fun uu____78390  ->
                                                       fun uu____78391  ->
                                                         match (uu____78390,
                                                                 uu____78391)
                                                         with
                                                         | ((x,uu____78417),
                                                            (y,uu____78419))
                                                             ->
                                                             let uu____78440
                                                               =
                                                               let uu____78447
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   y
                                                                  in
                                                               (x,
                                                                 uu____78447)
                                                                in
                                                             FStar_Syntax_Syntax.NT
                                                               uu____78440)
                                                    tbinders targs
                                                   in
                                                FStar_Syntax_Subst.subst s
                                                  tbody
                                                 in
                                              let env =
                                                FStar_List.fold_left
                                                  (fun env  ->
                                                     fun uu____78464  ->
                                                       match uu____78464 with
                                                       | (a,uu____78472) ->
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
                                                let uu____78483 =
                                                  FStar_All.pipe_right targs
                                                    (FStar_List.map
                                                       (fun uu____78502  ->
                                                          match uu____78502
                                                          with
                                                          | (x,uu____78511)
                                                              ->
                                                              FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                                x))
                                                   in
                                                (uu____78483, expected_t)  in
                                              let add_unit =
                                                match rest_args with
                                                | [] ->
                                                    (let uu____78527 =
                                                       is_fstar_value body1
                                                        in
                                                     Prims.op_Negation
                                                       uu____78527)
                                                      ||
                                                      (let uu____78530 =
                                                         FStar_Syntax_Util.is_pure_comp
                                                           c1
                                                          in
                                                       Prims.op_Negation
                                                         uu____78530)
                                                | uu____78532 -> false  in
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
                              | FStar_Syntax_Syntax.Tm_uinst uu____78594 ->
                                  let env =
                                    FStar_List.fold_left
                                      (fun env  ->
                                         fun uu____78613  ->
                                           match uu____78613 with
                                           | (a,uu____78621) ->
                                               FStar_Extraction_ML_UEnv.extend_ty
                                                 env a
                                                 FStar_Pervasives_Native.None)
                                      g tbinders
                                     in
                                  let expected_t = term_as_mlty env tbody  in
                                  let polytype =
                                    let uu____78632 =
                                      FStar_All.pipe_right tbinders
                                        (FStar_List.map
                                           (fun uu____78651  ->
                                              match uu____78651 with
                                              | (x,uu____78660) ->
                                                  FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                    x))
                                       in
                                    (uu____78632, expected_t)  in
                                  let args =
                                    FStar_All.pipe_right tbinders
                                      (FStar_List.map
                                         (fun uu____78704  ->
                                            match uu____78704 with
                                            | (bv,uu____78712) ->
                                                let uu____78717 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    bv
                                                   in
                                                FStar_All.pipe_right
                                                  uu____78717
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
                              | FStar_Syntax_Syntax.Tm_fvar uu____78747 ->
                                  let env =
                                    FStar_List.fold_left
                                      (fun env  ->
                                         fun uu____78760  ->
                                           match uu____78760 with
                                           | (a,uu____78768) ->
                                               FStar_Extraction_ML_UEnv.extend_ty
                                                 env a
                                                 FStar_Pervasives_Native.None)
                                      g tbinders
                                     in
                                  let expected_t = term_as_mlty env tbody  in
                                  let polytype =
                                    let uu____78779 =
                                      FStar_All.pipe_right tbinders
                                        (FStar_List.map
                                           (fun uu____78798  ->
                                              match uu____78798 with
                                              | (x,uu____78807) ->
                                                  FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                    x))
                                       in
                                    (uu____78779, expected_t)  in
                                  let args =
                                    FStar_All.pipe_right tbinders
                                      (FStar_List.map
                                         (fun uu____78851  ->
                                            match uu____78851 with
                                            | (bv,uu____78859) ->
                                                let uu____78864 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    bv
                                                   in
                                                FStar_All.pipe_right
                                                  uu____78864
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
                              | FStar_Syntax_Syntax.Tm_name uu____78894 ->
                                  let env =
                                    FStar_List.fold_left
                                      (fun env  ->
                                         fun uu____78907  ->
                                           match uu____78907 with
                                           | (a,uu____78915) ->
                                               FStar_Extraction_ML_UEnv.extend_ty
                                                 env a
                                                 FStar_Pervasives_Native.None)
                                      g tbinders
                                     in
                                  let expected_t = term_as_mlty env tbody  in
                                  let polytype =
                                    let uu____78926 =
                                      FStar_All.pipe_right tbinders
                                        (FStar_List.map
                                           (fun uu____78945  ->
                                              match uu____78945 with
                                              | (x,uu____78954) ->
                                                  FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                    x))
                                       in
                                    (uu____78926, expected_t)  in
                                  let args =
                                    FStar_All.pipe_right tbinders
                                      (FStar_List.map
                                         (fun uu____78998  ->
                                            match uu____78998 with
                                            | (bv,uu____79006) ->
                                                let uu____79011 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    bv
                                                   in
                                                FStar_All.pipe_right
                                                  uu____79011
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
                              | uu____79041 -> err_value_restriction lbdef1)))
               | uu____79061 -> no_gen ())
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
           fun uu____79212  ->
             match uu____79212 with
             | (lbname,e_tag,(typ,(binders,mltyscheme)),add_unit,_body) ->
                 let uu____79273 =
                   FStar_Extraction_ML_UEnv.extend_lb env lbname typ
                     mltyscheme add_unit is_rec
                    in
                 (match uu____79273 with
                  | (env1,uu____79290,exp_binding) ->
                      let uu____79294 =
                        let uu____79299 = FStar_Util.right lbname  in
                        (uu____79299, exp_binding)  in
                      (env1, uu____79294))) g lbs1
  
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
            (fun uu____79365  ->
               let uu____79366 = FStar_Syntax_Print.term_to_string e  in
               let uu____79368 =
                 FStar_Extraction_ML_Code.string_of_mlty
                   g.FStar_Extraction_ML_UEnv.currentModule ty
                  in
               FStar_Util.print2 "Checking %s at type %s\n" uu____79366
                 uu____79368);
          (match (f, ty) with
           | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____79375) ->
               (FStar_Extraction_ML_Syntax.ml_unit,
                 FStar_Extraction_ML_Syntax.MLTY_Erased)
           | (FStar_Extraction_ML_Syntax.E_PURE
              ,FStar_Extraction_ML_Syntax.MLTY_Erased ) ->
               (FStar_Extraction_ML_Syntax.ml_unit,
                 FStar_Extraction_ML_Syntax.MLTY_Erased)
           | uu____79376 ->
               let uu____79381 = term_as_mlexpr g e  in
               (match uu____79381 with
                | (ml_e,tag,t) ->
                    let uu____79395 = maybe_promote_effect ml_e tag t  in
                    (match uu____79395 with
                     | (ml_e1,tag1) ->
                         let uu____79406 =
                           FStar_Extraction_ML_Util.eff_leq tag1 f  in
                         if uu____79406
                         then
                           let uu____79413 =
                             maybe_coerce e.FStar_Syntax_Syntax.pos g ml_e1 t
                               ty
                              in
                           (uu____79413, ty)
                         else
                           (match (tag1, f, ty) with
                            | (FStar_Extraction_ML_Syntax.E_GHOST
                               ,FStar_Extraction_ML_Syntax.E_PURE
                               ,FStar_Extraction_ML_Syntax.MLTY_Erased ) ->
                                let uu____79420 =
                                  maybe_coerce e.FStar_Syntax_Syntax.pos g
                                    ml_e1 t ty
                                   in
                                (uu____79420, ty)
                            | uu____79421 ->
                                (err_unexpected_eff g e ty f tag1;
                                 (let uu____79429 =
                                    maybe_coerce e.FStar_Syntax_Syntax.pos g
                                      ml_e1 t ty
                                     in
                                  (uu____79429, ty)))))))

and (term_as_mlexpr :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag *
        FStar_Extraction_ML_Syntax.mlty))
  =
  fun g  ->
    fun e  ->
      let uu____79432 = term_as_mlexpr' g e  in
      match uu____79432 with
      | (e1,f,t) ->
          let uu____79448 = maybe_promote_effect e1 f t  in
          (match uu____79448 with | (e2,f1) -> (e2, f1, t))

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
           let uu____79473 =
             let uu____79475 =
               FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos  in
             let uu____79477 = FStar_Syntax_Print.tag_of_term top  in
             let uu____79479 = FStar_Syntax_Print.term_to_string top  in
             FStar_Util.format3 "%s: term_as_mlexpr' (%s) :  %s \n"
               uu____79475 uu____79477 uu____79479
              in
           FStar_Util.print_string uu____79473);
      (let t = FStar_Syntax_Subst.compress top  in
       match t.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____79489 =
             let uu____79491 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____79491
              in
           failwith uu____79489
       | FStar_Syntax_Syntax.Tm_delayed uu____79500 ->
           let uu____79523 =
             let uu____79525 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____79525
              in
           failwith uu____79523
       | FStar_Syntax_Syntax.Tm_uvar uu____79534 ->
           let uu____79547 =
             let uu____79549 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____79549
              in
           failwith uu____79547
       | FStar_Syntax_Syntax.Tm_bvar uu____79558 ->
           let uu____79559 =
             let uu____79561 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____79561
              in
           failwith uu____79559
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____79571 = FStar_Syntax_Util.unfold_lazy i  in
           term_as_mlexpr g uu____79571
       | FStar_Syntax_Syntax.Tm_type uu____79572 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_refine uu____79573 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_arrow uu____79580 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_quoted
           (qt,{
                 FStar_Syntax_Syntax.qkind =
                   FStar_Syntax_Syntax.Quote_dynamic ;
                 FStar_Syntax_Syntax.antiquotes = uu____79596;_})
           ->
           let uu____79609 =
             let uu____79610 =
               FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.failwith_lid
                 FStar_Syntax_Syntax.delta_constant
                 FStar_Pervasives_Native.None
                in
             FStar_Extraction_ML_UEnv.lookup_fv g uu____79610  in
           (match uu____79609 with
            | { FStar_Extraction_ML_UEnv.exp_b_name = uu____79617;
                FStar_Extraction_ML_UEnv.exp_b_expr = fw;
                FStar_Extraction_ML_UEnv.exp_b_tscheme = uu____79619;
                FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____79620;_} ->
                let uu____79623 =
                  let uu____79624 =
                    let uu____79625 =
                      let uu____79632 =
                        let uu____79635 =
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty
                               FStar_Extraction_ML_Syntax.ml_string_ty)
                            (FStar_Extraction_ML_Syntax.MLE_Const
                               (FStar_Extraction_ML_Syntax.MLC_String
                                  "Cannot evaluate open quotation at runtime"))
                           in
                        [uu____79635]  in
                      (fw, uu____79632)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____79625  in
                  FStar_All.pipe_left
                    (FStar_Extraction_ML_Syntax.with_ty
                       FStar_Extraction_ML_Syntax.ml_int_ty) uu____79624
                   in
                (uu____79623, FStar_Extraction_ML_Syntax.E_PURE,
                  FStar_Extraction_ML_Syntax.ml_int_ty))
       | FStar_Syntax_Syntax.Tm_quoted
           (qt,{
                 FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static ;
                 FStar_Syntax_Syntax.antiquotes = aqs;_})
           ->
           let uu____79653 = FStar_Reflection_Basic.inspect_ln qt  in
           (match uu____79653 with
            | FStar_Reflection_Data.Tv_Var bv ->
                let uu____79661 = FStar_Syntax_Syntax.lookup_aq bv aqs  in
                (match uu____79661 with
                 | FStar_Pervasives_Native.Some tm -> term_as_mlexpr g tm
                 | FStar_Pervasives_Native.None  ->
                     let tv =
                       let uu____79672 =
                         let uu____79679 =
                           FStar_Reflection_Embeddings.e_term_view_aq aqs  in
                         FStar_Syntax_Embeddings.embed uu____79679
                           (FStar_Reflection_Data.Tv_Var bv)
                          in
                       uu____79672 t.FStar_Syntax_Syntax.pos
                         FStar_Pervasives_Native.None
                         FStar_Syntax_Embeddings.id_norm_cb
                        in
                     let t1 =
                       let uu____79710 =
                         let uu____79721 = FStar_Syntax_Syntax.as_arg tv  in
                         [uu____79721]  in
                       FStar_Syntax_Util.mk_app
                         (FStar_Reflection_Data.refl_constant_term
                            FStar_Reflection_Data.fstar_refl_pack_ln)
                         uu____79710
                        in
                     term_as_mlexpr g t1)
            | tv ->
                let tv1 =
                  let uu____79748 =
                    let uu____79755 =
                      FStar_Reflection_Embeddings.e_term_view_aq aqs  in
                    FStar_Syntax_Embeddings.embed uu____79755 tv  in
                  uu____79748 t.FStar_Syntax_Syntax.pos
                    FStar_Pervasives_Native.None
                    FStar_Syntax_Embeddings.id_norm_cb
                   in
                let t1 =
                  let uu____79786 =
                    let uu____79797 = FStar_Syntax_Syntax.as_arg tv1  in
                    [uu____79797]  in
                  FStar_Syntax_Util.mk_app
                    (FStar_Reflection_Data.refl_constant_term
                       FStar_Reflection_Data.fstar_refl_pack_ln) uu____79786
                   in
                term_as_mlexpr g t1)
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_monadic (m,uu____79824)) ->
           let t2 = FStar_Syntax_Subst.compress t1  in
           (match t2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) when
                FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname ->
                let uu____79857 =
                  let uu____79864 =
                    FStar_TypeChecker_Env.effect_decl_opt
                      g.FStar_Extraction_ML_UEnv.env_tcenv m
                     in
                  FStar_Util.must uu____79864  in
                (match uu____79857 with
                 | (ed,qualifiers) ->
                     let uu____79891 =
                       let uu____79893 =
                         FStar_TypeChecker_Env.is_reifiable_effect
                           g.FStar_Extraction_ML_UEnv.env_tcenv
                           ed.FStar_Syntax_Syntax.mname
                          in
                       Prims.op_Negation uu____79893  in
                     if uu____79891
                     then term_as_mlexpr g t2
                     else
                       failwith
                         "This should not happen (should have been handled at Tm_abs level)")
            | uu____79911 -> term_as_mlexpr g t2)
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____79913) -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____79919) -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____79925 =
             FStar_TypeChecker_TcTerm.type_of_tot_term
               g.FStar_Extraction_ML_UEnv.env_tcenv t
              in
           (match uu____79925 with
            | (uu____79938,ty,uu____79940) ->
                let ml_ty = term_as_mlty g ty  in
                let uu____79942 =
                  let uu____79943 =
                    FStar_Extraction_ML_Util.mlexpr_of_const
                      t.FStar_Syntax_Syntax.pos c
                     in
                  FStar_Extraction_ML_Syntax.with_ty ml_ty uu____79943  in
                (uu____79942, FStar_Extraction_ML_Syntax.E_PURE, ml_ty))
       | FStar_Syntax_Syntax.Tm_name uu____79944 ->
           let uu____79945 = is_type g t  in
           if uu____79945
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____79956 = FStar_Extraction_ML_UEnv.lookup_term g t  in
              match uu____79956 with
              | (FStar_Util.Inl uu____79969,uu____79970) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | (FStar_Util.Inr
                 { FStar_Extraction_ML_UEnv.exp_b_name = uu____79975;
                   FStar_Extraction_ML_UEnv.exp_b_expr = x;
                   FStar_Extraction_ML_UEnv.exp_b_tscheme = mltys;
                   FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____79978;_},qual)
                  ->
                  (match mltys with
                   | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                       ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | ([],t1) ->
                       let uu____79996 =
                         maybe_eta_data_and_project_record g qual t1 x  in
                       (uu____79996, FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | uu____79997 -> err_uninst g t mltys t))
       | FStar_Syntax_Syntax.Tm_fvar fv ->
           let uu____80005 = is_type g t  in
           if uu____80005
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____80016 = FStar_Extraction_ML_UEnv.try_lookup_fv g fv
                 in
              match uu____80016 with
              | FStar_Pervasives_Native.None  ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.MLTY_Erased)
              | FStar_Pervasives_Native.Some
                  { FStar_Extraction_ML_UEnv.exp_b_name = uu____80025;
                    FStar_Extraction_ML_UEnv.exp_b_expr = x;
                    FStar_Extraction_ML_UEnv.exp_b_tscheme = mltys;
                    FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____80028;_}
                  ->
                  (FStar_Extraction_ML_UEnv.debug g
                     (fun uu____80036  ->
                        let uu____80037 = FStar_Syntax_Print.fv_to_string fv
                           in
                        let uu____80039 =
                          FStar_Extraction_ML_Code.string_of_mlexpr
                            g.FStar_Extraction_ML_UEnv.currentModule x
                           in
                        let uu____80041 =
                          FStar_Extraction_ML_Code.string_of_mlty
                            g.FStar_Extraction_ML_UEnv.currentModule
                            (FStar_Pervasives_Native.snd mltys)
                           in
                        FStar_Util.print3 "looked up %s: got %s at %s \n"
                          uu____80037 uu____80039 uu____80041);
                   (match mltys with
                    | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                        ->
                        (FStar_Extraction_ML_Syntax.ml_unit,
                          FStar_Extraction_ML_Syntax.E_PURE, t1)
                    | ([],t1) ->
                        let uu____80054 =
                          maybe_eta_data_and_project_record g
                            fv.FStar_Syntax_Syntax.fv_qual t1 x
                           in
                        (uu____80054, FStar_Extraction_ML_Syntax.E_PURE, t1)
                    | uu____80055 -> err_uninst g t mltys t)))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,rcopt) ->
           let uu____80089 = FStar_Syntax_Subst.open_term bs body  in
           (match uu____80089 with
            | (bs1,body1) ->
                let uu____80102 = binders_as_ml_binders g bs1  in
                (match uu____80102 with
                 | (ml_bs,env) ->
                     let body2 =
                       match rcopt with
                       | FStar_Pervasives_Native.Some rc ->
                           let uu____80138 =
                             FStar_TypeChecker_Env.is_reifiable_rc
                               env.FStar_Extraction_ML_UEnv.env_tcenv rc
                              in
                           if uu____80138
                           then
                             FStar_TypeChecker_Util.reify_body
                               env.FStar_Extraction_ML_UEnv.env_tcenv body1
                           else body1
                       | FStar_Pervasives_Native.None  ->
                           (FStar_Extraction_ML_UEnv.debug g
                              (fun uu____80146  ->
                                 let uu____80147 =
                                   FStar_Syntax_Print.term_to_string body1
                                    in
                                 FStar_Util.print1
                                   "No computation type for: %s\n"
                                   uu____80147);
                            body1)
                        in
                     let uu____80150 = term_as_mlexpr env body2  in
                     (match uu____80150 with
                      | (ml_body,f,t1) ->
                          let uu____80166 =
                            FStar_List.fold_right
                              (fun uu____80186  ->
                                 fun uu____80187  ->
                                   match (uu____80186, uu____80187) with
                                   | ((uu____80210,targ),(f1,t2)) ->
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         (FStar_Extraction_ML_Syntax.MLTY_Fun
                                            (targ, f1, t2)))) ml_bs (f, t1)
                             in
                          (match uu____80166 with
                           | (f1,tfun) ->
                               let uu____80233 =
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty tfun)
                                   (FStar_Extraction_ML_Syntax.MLE_Fun
                                      (ml_bs, ml_body))
                                  in
                               (uu____80233, f1, tfun)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____80241;
              FStar_Syntax_Syntax.vars = uu____80242;_},(a1,uu____80244)::[])
           ->
           let ty =
             let uu____80284 =
               FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid  in
             term_as_mlty g uu____80284  in
           let uu____80285 =
             let uu____80286 =
               FStar_Extraction_ML_Util.mlexpr_of_range
                 a1.FStar_Syntax_Syntax.pos
                in
             FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty)
               uu____80286
              in
           (uu____80285, FStar_Extraction_ML_Syntax.E_PURE, ty)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____80287;
              FStar_Syntax_Syntax.vars = uu____80288;_},(t1,uu____80290)::
            (r,uu____80292)::[])
           -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____80347);
              FStar_Syntax_Syntax.pos = uu____80348;
              FStar_Syntax_Syntax.vars = uu____80349;_},uu____80350)
           -> failwith "Unreachable? Tm_app Const_reflect"
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let is_total rc =
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_Tot_lid)
               ||
               (FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
                  (FStar_List.existsb
                     (fun uu___619_80419  ->
                        match uu___619_80419 with
                        | FStar_Syntax_Syntax.TOTAL  -> true
                        | uu____80422 -> false)))
              in
           let uu____80424 =
             let uu____80429 =
               let uu____80430 = FStar_Syntax_Subst.compress head1  in
               uu____80430.FStar_Syntax_Syntax.n  in
             ((head1.FStar_Syntax_Syntax.n), uu____80429)  in
           (match uu____80424 with
            | (FStar_Syntax_Syntax.Tm_uvar uu____80439,uu____80440) ->
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
            | (uu____80454,FStar_Syntax_Syntax.Tm_abs
               (bs,uu____80456,FStar_Pervasives_Native.Some rc)) when
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
            | (uu____80481,FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_reify )) ->
                let e =
                  let uu____80483 = FStar_List.hd args  in
                  FStar_TypeChecker_Util.reify_body_with_arg
                    g.FStar_Extraction_ML_UEnv.env_tcenv head1 uu____80483
                   in
                let tm =
                  let uu____80495 =
                    let uu____80500 = FStar_TypeChecker_Util.remove_reify e
                       in
                    let uu____80501 = FStar_List.tl args  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____80500 uu____80501  in
                  uu____80495 FStar_Pervasives_Native.None
                    t.FStar_Syntax_Syntax.pos
                   in
                term_as_mlexpr g tm
            | uu____80512 ->
                let rec extract_app is_data uu____80565 uu____80566 restArgs
                  =
                  match (uu____80565, uu____80566) with
                  | ((mlhead,mlargs_f),(f,t1)) ->
                      let mk_head uu____80647 =
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
                         (fun uu____80674  ->
                            let uu____80675 =
                              let uu____80677 = mk_head ()  in
                              FStar_Extraction_ML_Code.string_of_mlexpr
                                g.FStar_Extraction_ML_UEnv.currentModule
                                uu____80677
                               in
                            let uu____80678 =
                              FStar_Extraction_ML_Code.string_of_mlty
                                g.FStar_Extraction_ML_UEnv.currentModule t1
                               in
                            let uu____80680 =
                              match restArgs with
                              | [] -> "none"
                              | (hd1,uu____80691)::uu____80692 ->
                                  FStar_Syntax_Print.term_to_string hd1
                               in
                            FStar_Util.print3
                              "extract_app ml_head=%s type of head = %s, next arg = %s\n"
                              uu____80675 uu____80678 uu____80680);
                       (match (restArgs, t1) with
                        | ([],uu____80726) ->
                            let app =
                              let uu____80742 = mk_head ()  in
                              maybe_eta_data_and_project_record g is_data t1
                                uu____80742
                               in
                            (app, f, t1)
                        | ((arg,uu____80744)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                           (formal_t,f',t2)) when
                            (is_type g arg) &&
                              (type_leq g formal_t
                                 FStar_Extraction_ML_Syntax.ml_unit_ty)
                            ->
                            let uu____80775 =
                              let uu____80780 =
                                FStar_Extraction_ML_Util.join
                                  arg.FStar_Syntax_Syntax.pos f f'
                                 in
                              (uu____80780, t2)  in
                            extract_app is_data
                              (mlhead,
                                ((FStar_Extraction_ML_Syntax.ml_unit,
                                   FStar_Extraction_ML_Syntax.E_PURE) ::
                                mlargs_f)) uu____80775 rest
                        | ((e0,uu____80792)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                           (tExpected,f',t2)) ->
                            let r = e0.FStar_Syntax_Syntax.pos  in
                            let expected_effect =
                              let uu____80825 =
                                (FStar_Options.lax ()) &&
                                  (FStar_TypeChecker_Util.short_circuit_head
                                     head1)
                                 in
                              if uu____80825
                              then FStar_Extraction_ML_Syntax.E_IMPURE
                              else FStar_Extraction_ML_Syntax.E_PURE  in
                            let uu____80830 =
                              check_term_as_mlexpr g e0 expected_effect
                                tExpected
                               in
                            (match uu____80830 with
                             | (e01,tInferred) ->
                                 let uu____80843 =
                                   let uu____80848 =
                                     FStar_Extraction_ML_Util.join_l r
                                       [f; f']
                                      in
                                   (uu____80848, t2)  in
                                 extract_app is_data
                                   (mlhead, ((e01, expected_effect) ::
                                     mlargs_f)) uu____80843 rest)
                        | uu____80859 ->
                            let uu____80872 =
                              FStar_Extraction_ML_Util.udelta_unfold g t1  in
                            (match uu____80872 with
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
                                  | uu____80944 ->
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
                let extract_app_maybe_projector is_data mlhead uu____81015
                  args1 =
                  match uu____81015 with
                  | (f,t1) ->
                      (match is_data with
                       | FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_projector uu____81045)
                           ->
                           let rec remove_implicits args2 f1 t2 =
                             match (args2, t2) with
                             | ((a0,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____81129))::args3,FStar_Extraction_ML_Syntax.MLTY_Fun
                                (uu____81131,f',t3)) ->
                                 let uu____81169 =
                                   FStar_Extraction_ML_Util.join
                                     a0.FStar_Syntax_Syntax.pos f1 f'
                                    in
                                 remove_implicits args3 uu____81169 t3
                             | uu____81170 -> (args2, f1, t2)  in
                           let uu____81195 = remove_implicits args1 f t1  in
                           (match uu____81195 with
                            | (args2,f1,t2) ->
                                extract_app is_data (mlhead, []) (f1, t2)
                                  args2)
                       | uu____81251 ->
                           extract_app is_data (mlhead, []) (f, t1) args1)
                   in
                let extract_app_with_instantiations uu____81275 =
                  let head2 = FStar_Syntax_Util.un_uinst head1  in
                  match head2.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_name uu____81283 ->
                      let uu____81284 =
                        let uu____81305 =
                          FStar_Extraction_ML_UEnv.lookup_term g head2  in
                        match uu____81305 with
                        | (FStar_Util.Inr exp_b,q) ->
                            (FStar_Extraction_ML_UEnv.debug g
                               (fun uu____81344  ->
                                  let uu____81345 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  let uu____81347 =
                                    FStar_Extraction_ML_Code.string_of_mlexpr
                                      g.FStar_Extraction_ML_UEnv.currentModule
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_expr
                                     in
                                  let uu____81349 =
                                    FStar_Extraction_ML_Code.string_of_mlty
                                      g.FStar_Extraction_ML_UEnv.currentModule
                                      (FStar_Pervasives_Native.snd
                                         exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme)
                                     in
                                  let uu____81351 =
                                    FStar_Util.string_of_bool
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok
                                     in
                                  FStar_Util.print4
                                    "@@@looked up %s: got %s at %s (inst_ok=%s)\n"
                                    uu____81345 uu____81347 uu____81349
                                    uu____81351);
                             (((exp_b.FStar_Extraction_ML_UEnv.exp_b_expr),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok)),
                               q))
                        | uu____81378 -> failwith "FIXME Ty"  in
                      (match uu____81284 with
                       | ((head_ml,(vars,t1),inst_ok),qual) ->
                           let has_typ_apps =
                             match args with
                             | (a,uu____81454)::uu____81455 -> is_type g a
                             | uu____81482 -> false  in
                           let uu____81494 =
                             match vars with
                             | uu____81523::uu____81524 when
                                 (Prims.op_Negation has_typ_apps) && inst_ok
                                 -> (head_ml, t1, args)
                             | uu____81538 ->
                                 let n1 = FStar_List.length vars  in
                                 if n1 <= (FStar_List.length args)
                                 then
                                   let uu____81573 =
                                     FStar_Util.first_N n1 args  in
                                   (match uu____81573 with
                                    | (prefix1,rest) ->
                                        let prefixAsMLTypes =
                                          FStar_List.map
                                            (fun uu____81678  ->
                                               match uu____81678 with
                                               | (x,uu____81686) ->
                                                   term_as_mlty g x) prefix1
                                           in
                                        let t2 =
                                          instantiate (vars, t1)
                                            prefixAsMLTypes
                                           in
                                        (FStar_Extraction_ML_UEnv.debug g
                                           (fun uu____81698  ->
                                              let uu____81699 =
                                                FStar_Syntax_Print.term_to_string
                                                  head2
                                                 in
                                              let uu____81701 =
                                                FStar_Syntax_Print.args_to_string
                                                  prefix1
                                                 in
                                              let uu____81703 =
                                                let uu____81705 =
                                                  FStar_List.map
                                                    (FStar_Extraction_ML_Code.string_of_mlty
                                                       g.FStar_Extraction_ML_UEnv.currentModule)
                                                    prefixAsMLTypes
                                                   in
                                                FStar_All.pipe_right
                                                  uu____81705
                                                  (FStar_String.concat ", ")
                                                 in
                                              let uu____81715 =
                                                FStar_Extraction_ML_Code.string_of_mlty
                                                  g.FStar_Extraction_ML_UEnv.currentModule
                                                  t2
                                                 in
                                              FStar_Util.print4
                                                "@@@looked up %s, instantiated with [%s] translated to [%s], got %s\n"
                                                uu____81699 uu____81701
                                                uu____81703 uu____81715);
                                         (let mk_tapp e ty_args =
                                            match ty_args with
                                            | [] -> e
                                            | uu____81733 ->
                                                let uu___2233_81736 = e  in
                                                {
                                                  FStar_Extraction_ML_Syntax.expr
                                                    =
                                                    (FStar_Extraction_ML_Syntax.MLE_TApp
                                                       (e, ty_args));
                                                  FStar_Extraction_ML_Syntax.mlty
                                                    =
                                                    (uu___2233_81736.FStar_Extraction_ML_Syntax.mlty);
                                                  FStar_Extraction_ML_Syntax.loc
                                                    =
                                                    (uu___2233_81736.FStar_Extraction_ML_Syntax.loc)
                                                }
                                             in
                                          let head3 =
                                            match head_ml.FStar_Extraction_ML_Syntax.expr
                                            with
                                            | FStar_Extraction_ML_Syntax.MLE_Name
                                                uu____81740 ->
                                                let uu___2239_81741 =
                                                  mk_tapp head_ml
                                                    prefixAsMLTypes
                                                   in
                                                {
                                                  FStar_Extraction_ML_Syntax.expr
                                                    =
                                                    (uu___2239_81741.FStar_Extraction_ML_Syntax.expr);
                                                  FStar_Extraction_ML_Syntax.mlty
                                                    = t2;
                                                  FStar_Extraction_ML_Syntax.loc
                                                    =
                                                    (uu___2239_81741.FStar_Extraction_ML_Syntax.loc)
                                                }
                                            | FStar_Extraction_ML_Syntax.MLE_Var
                                                uu____81742 ->
                                                let uu___2239_81744 =
                                                  mk_tapp head_ml
                                                    prefixAsMLTypes
                                                   in
                                                {
                                                  FStar_Extraction_ML_Syntax.expr
                                                    =
                                                    (uu___2239_81744.FStar_Extraction_ML_Syntax.expr);
                                                  FStar_Extraction_ML_Syntax.mlty
                                                    = t2;
                                                  FStar_Extraction_ML_Syntax.loc
                                                    =
                                                    (uu___2239_81744.FStar_Extraction_ML_Syntax.loc)
                                                }
                                            | FStar_Extraction_ML_Syntax.MLE_App
                                                (head3,{
                                                         FStar_Extraction_ML_Syntax.expr
                                                           =
                                                           FStar_Extraction_ML_Syntax.MLE_Const
                                                           (FStar_Extraction_ML_Syntax.MLC_Unit
                                                           );
                                                         FStar_Extraction_ML_Syntax.mlty
                                                           = uu____81746;
                                                         FStar_Extraction_ML_Syntax.loc
                                                           = uu____81747;_}::[])
                                                ->
                                                FStar_All.pipe_right
                                                  (FStar_Extraction_ML_Syntax.MLE_App
                                                     ((let uu___2250_81753 =
                                                         mk_tapp head3
                                                           prefixAsMLTypes
                                                          in
                                                       {
                                                         FStar_Extraction_ML_Syntax.expr
                                                           =
                                                           (uu___2250_81753.FStar_Extraction_ML_Syntax.expr);
                                                         FStar_Extraction_ML_Syntax.mlty
                                                           =
                                                           (FStar_Extraction_ML_Syntax.MLTY_Fun
                                                              (FStar_Extraction_ML_Syntax.ml_unit_ty,
                                                                FStar_Extraction_ML_Syntax.E_PURE,
                                                                t2));
                                                         FStar_Extraction_ML_Syntax.loc
                                                           =
                                                           (uu___2250_81753.FStar_Extraction_ML_Syntax.loc)
                                                       }),
                                                       [FStar_Extraction_ML_Syntax.ml_unit]))
                                                  (FStar_Extraction_ML_Syntax.with_ty
                                                     t2)
                                            | uu____81754 ->
                                                failwith
                                                  "Impossible: Unexpected head term"
                                             in
                                          (head3, t2, rest))))
                                 else err_uninst g head2 (vars, t1) top
                              in
                           (match uu____81494 with
                            | (head_ml1,head_t,args1) ->
                                (match args1 with
                                 | [] ->
                                     let uu____81820 =
                                       maybe_eta_data_and_project_record g
                                         qual head_t head_ml1
                                        in
                                     (uu____81820,
                                       FStar_Extraction_ML_Syntax.E_PURE,
                                       head_t)
                                 | uu____81821 ->
                                     extract_app_maybe_projector qual
                                       head_ml1
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         head_t) args1)))
                  | FStar_Syntax_Syntax.Tm_fvar uu____81830 ->
                      let uu____81831 =
                        let uu____81852 =
                          FStar_Extraction_ML_UEnv.lookup_term g head2  in
                        match uu____81852 with
                        | (FStar_Util.Inr exp_b,q) ->
                            (FStar_Extraction_ML_UEnv.debug g
                               (fun uu____81891  ->
                                  let uu____81892 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  let uu____81894 =
                                    FStar_Extraction_ML_Code.string_of_mlexpr
                                      g.FStar_Extraction_ML_UEnv.currentModule
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_expr
                                     in
                                  let uu____81896 =
                                    FStar_Extraction_ML_Code.string_of_mlty
                                      g.FStar_Extraction_ML_UEnv.currentModule
                                      (FStar_Pervasives_Native.snd
                                         exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme)
                                     in
                                  let uu____81898 =
                                    FStar_Util.string_of_bool
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok
                                     in
                                  FStar_Util.print4
                                    "@@@looked up %s: got %s at %s (inst_ok=%s)\n"
                                    uu____81892 uu____81894 uu____81896
                                    uu____81898);
                             (((exp_b.FStar_Extraction_ML_UEnv.exp_b_expr),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok)),
                               q))
                        | uu____81925 -> failwith "FIXME Ty"  in
                      (match uu____81831 with
                       | ((head_ml,(vars,t1),inst_ok),qual) ->
                           let has_typ_apps =
                             match args with
                             | (a,uu____82001)::uu____82002 -> is_type g a
                             | uu____82029 -> false  in
                           let uu____82041 =
                             match vars with
                             | uu____82070::uu____82071 when
                                 (Prims.op_Negation has_typ_apps) && inst_ok
                                 -> (head_ml, t1, args)
                             | uu____82085 ->
                                 let n1 = FStar_List.length vars  in
                                 if n1 <= (FStar_List.length args)
                                 then
                                   let uu____82120 =
                                     FStar_Util.first_N n1 args  in
                                   (match uu____82120 with
                                    | (prefix1,rest) ->
                                        let prefixAsMLTypes =
                                          FStar_List.map
                                            (fun uu____82225  ->
                                               match uu____82225 with
                                               | (x,uu____82233) ->
                                                   term_as_mlty g x) prefix1
                                           in
                                        let t2 =
                                          instantiate (vars, t1)
                                            prefixAsMLTypes
                                           in
                                        (FStar_Extraction_ML_UEnv.debug g
                                           (fun uu____82245  ->
                                              let uu____82246 =
                                                FStar_Syntax_Print.term_to_string
                                                  head2
                                                 in
                                              let uu____82248 =
                                                FStar_Syntax_Print.args_to_string
                                                  prefix1
                                                 in
                                              let uu____82250 =
                                                let uu____82252 =
                                                  FStar_List.map
                                                    (FStar_Extraction_ML_Code.string_of_mlty
                                                       g.FStar_Extraction_ML_UEnv.currentModule)
                                                    prefixAsMLTypes
                                                   in
                                                FStar_All.pipe_right
                                                  uu____82252
                                                  (FStar_String.concat ", ")
                                                 in
                                              let uu____82262 =
                                                FStar_Extraction_ML_Code.string_of_mlty
                                                  g.FStar_Extraction_ML_UEnv.currentModule
                                                  t2
                                                 in
                                              FStar_Util.print4
                                                "@@@looked up %s, instantiated with [%s] translated to [%s], got %s\n"
                                                uu____82246 uu____82248
                                                uu____82250 uu____82262);
                                         (let mk_tapp e ty_args =
                                            match ty_args with
                                            | [] -> e
                                            | uu____82280 ->
                                                let uu___2233_82283 = e  in
                                                {
                                                  FStar_Extraction_ML_Syntax.expr
                                                    =
                                                    (FStar_Extraction_ML_Syntax.MLE_TApp
                                                       (e, ty_args));
                                                  FStar_Extraction_ML_Syntax.mlty
                                                    =
                                                    (uu___2233_82283.FStar_Extraction_ML_Syntax.mlty);
                                                  FStar_Extraction_ML_Syntax.loc
                                                    =
                                                    (uu___2233_82283.FStar_Extraction_ML_Syntax.loc)
                                                }
                                             in
                                          let head3 =
                                            match head_ml.FStar_Extraction_ML_Syntax.expr
                                            with
                                            | FStar_Extraction_ML_Syntax.MLE_Name
                                                uu____82287 ->
                                                let uu___2239_82288 =
                                                  mk_tapp head_ml
                                                    prefixAsMLTypes
                                                   in
                                                {
                                                  FStar_Extraction_ML_Syntax.expr
                                                    =
                                                    (uu___2239_82288.FStar_Extraction_ML_Syntax.expr);
                                                  FStar_Extraction_ML_Syntax.mlty
                                                    = t2;
                                                  FStar_Extraction_ML_Syntax.loc
                                                    =
                                                    (uu___2239_82288.FStar_Extraction_ML_Syntax.loc)
                                                }
                                            | FStar_Extraction_ML_Syntax.MLE_Var
                                                uu____82289 ->
                                                let uu___2239_82291 =
                                                  mk_tapp head_ml
                                                    prefixAsMLTypes
                                                   in
                                                {
                                                  FStar_Extraction_ML_Syntax.expr
                                                    =
                                                    (uu___2239_82291.FStar_Extraction_ML_Syntax.expr);
                                                  FStar_Extraction_ML_Syntax.mlty
                                                    = t2;
                                                  FStar_Extraction_ML_Syntax.loc
                                                    =
                                                    (uu___2239_82291.FStar_Extraction_ML_Syntax.loc)
                                                }
                                            | FStar_Extraction_ML_Syntax.MLE_App
                                                (head3,{
                                                         FStar_Extraction_ML_Syntax.expr
                                                           =
                                                           FStar_Extraction_ML_Syntax.MLE_Const
                                                           (FStar_Extraction_ML_Syntax.MLC_Unit
                                                           );
                                                         FStar_Extraction_ML_Syntax.mlty
                                                           = uu____82293;
                                                         FStar_Extraction_ML_Syntax.loc
                                                           = uu____82294;_}::[])
                                                ->
                                                FStar_All.pipe_right
                                                  (FStar_Extraction_ML_Syntax.MLE_App
                                                     ((let uu___2250_82300 =
                                                         mk_tapp head3
                                                           prefixAsMLTypes
                                                          in
                                                       {
                                                         FStar_Extraction_ML_Syntax.expr
                                                           =
                                                           (uu___2250_82300.FStar_Extraction_ML_Syntax.expr);
                                                         FStar_Extraction_ML_Syntax.mlty
                                                           =
                                                           (FStar_Extraction_ML_Syntax.MLTY_Fun
                                                              (FStar_Extraction_ML_Syntax.ml_unit_ty,
                                                                FStar_Extraction_ML_Syntax.E_PURE,
                                                                t2));
                                                         FStar_Extraction_ML_Syntax.loc
                                                           =
                                                           (uu___2250_82300.FStar_Extraction_ML_Syntax.loc)
                                                       }),
                                                       [FStar_Extraction_ML_Syntax.ml_unit]))
                                                  (FStar_Extraction_ML_Syntax.with_ty
                                                     t2)
                                            | uu____82301 ->
                                                failwith
                                                  "Impossible: Unexpected head term"
                                             in
                                          (head3, t2, rest))))
                                 else err_uninst g head2 (vars, t1) top
                              in
                           (match uu____82041 with
                            | (head_ml1,head_t,args1) ->
                                (match args1 with
                                 | [] ->
                                     let uu____82367 =
                                       maybe_eta_data_and_project_record g
                                         qual head_t head_ml1
                                        in
                                     (uu____82367,
                                       FStar_Extraction_ML_Syntax.E_PURE,
                                       head_t)
                                 | uu____82368 ->
                                     extract_app_maybe_projector qual
                                       head_ml1
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         head_t) args1)))
                  | uu____82377 ->
                      let uu____82378 = term_as_mlexpr g head2  in
                      (match uu____82378 with
                       | (head3,f,t1) ->
                           extract_app_maybe_projector
                             FStar_Pervasives_Native.None head3 (f, t1) args)
                   in
                let uu____82394 = is_type g t  in
                if uu____82394
                then
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
                else
                  (let uu____82405 =
                     let uu____82406 = FStar_Syntax_Util.un_uinst head1  in
                     uu____82406.FStar_Syntax_Syntax.n  in
                   match uu____82405 with
                   | FStar_Syntax_Syntax.Tm_fvar fv ->
                       let uu____82416 =
                         FStar_Extraction_ML_UEnv.try_lookup_fv g fv  in
                       (match uu____82416 with
                        | FStar_Pervasives_Native.None  ->
                            (FStar_Extraction_ML_Syntax.ml_unit,
                              FStar_Extraction_ML_Syntax.E_PURE,
                              FStar_Extraction_ML_Syntax.MLTY_Erased)
                        | uu____82425 -> extract_app_with_instantiations ())
                   | uu____82428 -> extract_app_with_instantiations ()))
       | FStar_Syntax_Syntax.Tm_ascribed (e0,(tc,uu____82431),f) ->
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
           let uu____82499 = check_term_as_mlexpr g e0 f1 t1  in
           (match uu____82499 with | (e,t2) -> (e, f1, t2))
       | FStar_Syntax_Syntax.Tm_let ((is_rec,lbs),e') ->
           let top_level = FStar_Syntax_Syntax.is_top_level lbs  in
           let uu____82534 =
             if is_rec
             then FStar_Syntax_Subst.open_let_rec lbs e'
             else
               (let uu____82550 = FStar_Syntax_Syntax.is_top_level lbs  in
                if uu____82550
                then (lbs, e')
                else
                  (let lb = FStar_List.hd lbs  in
                   let x =
                     let uu____82565 =
                       FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                     FStar_Syntax_Syntax.freshen_bv uu____82565  in
                   let lb1 =
                     let uu___2301_82567 = lb  in
                     {
                       FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                       FStar_Syntax_Syntax.lbunivs =
                         (uu___2301_82567.FStar_Syntax_Syntax.lbunivs);
                       FStar_Syntax_Syntax.lbtyp =
                         (uu___2301_82567.FStar_Syntax_Syntax.lbtyp);
                       FStar_Syntax_Syntax.lbeff =
                         (uu___2301_82567.FStar_Syntax_Syntax.lbeff);
                       FStar_Syntax_Syntax.lbdef =
                         (uu___2301_82567.FStar_Syntax_Syntax.lbdef);
                       FStar_Syntax_Syntax.lbattrs =
                         (uu___2301_82567.FStar_Syntax_Syntax.lbattrs);
                       FStar_Syntax_Syntax.lbpos =
                         (uu___2301_82567.FStar_Syntax_Syntax.lbpos)
                     }  in
                   let e'1 =
                     FStar_Syntax_Subst.subst
                       [FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x)] e'
                      in
                   ([lb1], e'1)))
              in
           (match uu____82534 with
            | (lbs1,e'1) ->
                let lbs2 =
                  if top_level
                  then
                    FStar_All.pipe_right lbs1
                      (FStar_List.map
                         (fun lb  ->
                            let tcenv =
                              let uu____82601 =
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
                                uu____82601
                               in
                            let lbdef =
                              let uu____82616 = FStar_Options.ml_ish ()  in
                              if uu____82616
                              then lb.FStar_Syntax_Syntax.lbdef
                              else
                                (let norm_call uu____82628 =
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
                                 let uu____82629 =
                                   (FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug tcenv)
                                      (FStar_Options.Other "Extraction"))
                                     ||
                                     (FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug tcenv)
                                        (FStar_Options.Other "ExtractNorm"))
                                    in
                                 if uu____82629
                                 then
                                   ((let uu____82639 =
                                       FStar_Syntax_Print.lbname_to_string
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     let uu____82641 =
                                       FStar_Syntax_Print.term_to_string
                                         lb.FStar_Syntax_Syntax.lbdef
                                        in
                                     FStar_Util.print2
                                       "Starting to normalize top-level let %s)\n\tlbdef=%s"
                                       uu____82639 uu____82641);
                                    (let a =
                                       let uu____82647 =
                                         let uu____82649 =
                                           FStar_Syntax_Print.lbname_to_string
                                             lb.FStar_Syntax_Syntax.lbname
                                            in
                                         FStar_Util.format1
                                           "###(Time to normalize top-level let %s)"
                                           uu____82649
                                          in
                                       FStar_Util.measure_execution_time
                                         uu____82647 norm_call
                                        in
                                     (let uu____82655 =
                                        FStar_Syntax_Print.term_to_string a
                                         in
                                      FStar_Util.print1 "Normalized to %s\n"
                                        uu____82655);
                                     a))
                                 else norm_call ())
                               in
                            let uu___2319_82660 = lb  in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___2319_82660.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___2319_82660.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp =
                                (uu___2319_82660.FStar_Syntax_Syntax.lbtyp);
                              FStar_Syntax_Syntax.lbeff =
                                (uu___2319_82660.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = lbdef;
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___2319_82660.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___2319_82660.FStar_Syntax_Syntax.lbpos)
                            }))
                  else lbs1  in
                let check_lb env uu____82713 =
                  match uu____82713 with
                  | (nm,(_lbname,f,(_t,(targs,polytype)),add_unit,e)) ->
                      let env1 =
                        FStar_List.fold_left
                          (fun env1  ->
                             fun uu____82869  ->
                               match uu____82869 with
                               | (a,uu____82877) ->
                                   FStar_Extraction_ML_UEnv.extend_ty env1 a
                                     FStar_Pervasives_Native.None) env targs
                         in
                      let expected_t = FStar_Pervasives_Native.snd polytype
                         in
                      let uu____82883 =
                        check_term_as_mlexpr env1 e f expected_t  in
                      (match uu____82883 with
                       | (e1,ty) ->
                           let uu____82894 =
                             maybe_promote_effect e1 f expected_t  in
                           (match uu____82894 with
                            | (e2,f1) ->
                                let meta =
                                  match (f1, ty) with
                                  | (FStar_Extraction_ML_Syntax.E_PURE
                                     ,FStar_Extraction_ML_Syntax.MLTY_Erased
                                     ) -> [FStar_Extraction_ML_Syntax.Erased]
                                  | (FStar_Extraction_ML_Syntax.E_GHOST
                                     ,FStar_Extraction_ML_Syntax.MLTY_Erased
                                     ) -> [FStar_Extraction_ML_Syntax.Erased]
                                  | uu____82906 -> []  in
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
                let uu____82937 =
                  FStar_List.fold_right
                    (fun lb  ->
                       fun uu____83034  ->
                         match uu____83034 with
                         | (env,lbs4) ->
                             let uu____83168 = lb  in
                             (match uu____83168 with
                              | (lbname,uu____83219,(t1,(uu____83221,polytype)),add_unit,uu____83224)
                                  ->
                                  let uu____83239 =
                                    FStar_Extraction_ML_UEnv.extend_lb env
                                      lbname t1 polytype add_unit true
                                     in
                                  (match uu____83239 with
                                   | (env1,nm,uu____83280) ->
                                       (env1, ((nm, lb) :: lbs4))))) lbs3
                    (g, [])
                   in
                (match uu____82937 with
                 | (env_body,lbs4) ->
                     let env_def = if is_rec then env_body else g  in
                     let lbs5 =
                       FStar_All.pipe_right lbs4
                         (FStar_List.map (check_lb env_def))
                        in
                     let e'_rng = e'1.FStar_Syntax_Syntax.pos  in
                     let uu____83559 = term_as_mlexpr env_body e'1  in
                     (match uu____83559 with
                      | (e'2,f',t') ->
                          let f =
                            let uu____83576 =
                              let uu____83579 =
                                FStar_List.map FStar_Pervasives_Native.fst
                                  lbs5
                                 in
                              f' :: uu____83579  in
                            FStar_Extraction_ML_Util.join_l e'_rng
                              uu____83576
                             in
                          let is_rec1 =
                            if is_rec = true
                            then FStar_Extraction_ML_Syntax.Rec
                            else FStar_Extraction_ML_Syntax.NonRec  in
                          let uu____83592 =
                            let uu____83593 =
                              let uu____83594 =
                                let uu____83595 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    lbs5
                                   in
                                (is_rec1, uu____83595)  in
                              mk_MLE_Let top_level uu____83594 e'2  in
                            let uu____83604 =
                              FStar_Extraction_ML_Util.mlloc_of_range
                                t.FStar_Syntax_Syntax.pos
                               in
                            FStar_Extraction_ML_Syntax.with_ty_loc t'
                              uu____83593 uu____83604
                             in
                          (uu____83592, f, t'))))
       | FStar_Syntax_Syntax.Tm_match (scrutinee,pats) ->
           let uu____83643 = term_as_mlexpr g scrutinee  in
           (match uu____83643 with
            | (e,f_e,t_e) ->
                let uu____83659 = check_pats_for_ite pats  in
                (match uu____83659 with
                 | (b,then_e,else_e) ->
                     let no_lift x t1 = x  in
                     if b
                     then
                       (match (then_e, else_e) with
                        | (FStar_Pervasives_Native.Some
                           then_e1,FStar_Pervasives_Native.Some else_e1) ->
                            let uu____83724 = term_as_mlexpr g then_e1  in
                            (match uu____83724 with
                             | (then_mle,f_then,t_then) ->
                                 let uu____83740 = term_as_mlexpr g else_e1
                                    in
                                 (match uu____83740 with
                                  | (else_mle,f_else,t_else) ->
                                      let uu____83756 =
                                        let uu____83767 =
                                          type_leq g t_then t_else  in
                                        if uu____83767
                                        then (t_else, no_lift)
                                        else
                                          (let uu____83788 =
                                             type_leq g t_else t_then  in
                                           if uu____83788
                                           then (t_then, no_lift)
                                           else
                                             (FStar_Extraction_ML_Syntax.MLTY_Top,
                                               FStar_Extraction_ML_Syntax.apply_obj_repr))
                                         in
                                      (match uu____83756 with
                                       | (t_branch,maybe_lift1) ->
                                           let uu____83835 =
                                             let uu____83836 =
                                               let uu____83837 =
                                                 let uu____83846 =
                                                   maybe_lift1 then_mle
                                                     t_then
                                                    in
                                                 let uu____83847 =
                                                   let uu____83850 =
                                                     maybe_lift1 else_mle
                                                       t_else
                                                      in
                                                   FStar_Pervasives_Native.Some
                                                     uu____83850
                                                    in
                                                 (e, uu____83846,
                                                   uu____83847)
                                                  in
                                               FStar_Extraction_ML_Syntax.MLE_If
                                                 uu____83837
                                                in
                                             FStar_All.pipe_left
                                               (FStar_Extraction_ML_Syntax.with_ty
                                                  t_branch) uu____83836
                                              in
                                           let uu____83853 =
                                             FStar_Extraction_ML_Util.join
                                               then_e1.FStar_Syntax_Syntax.pos
                                               f_then f_else
                                              in
                                           (uu____83835, uu____83853,
                                             t_branch))))
                        | uu____83854 ->
                            failwith
                              "ITE pats matched but then and else expressions not found?")
                     else
                       (let uu____83872 =
                          FStar_All.pipe_right pats
                            (FStar_Util.fold_map
                               (fun compat  ->
                                  fun br  ->
                                    let uu____83971 =
                                      FStar_Syntax_Subst.open_branch br  in
                                    match uu____83971 with
                                    | (pat,when_opt,branch1) ->
                                        let uu____84016 =
                                          extract_pat g pat t_e
                                            term_as_mlexpr
                                           in
                                        (match uu____84016 with
                                         | (env,p,pat_t_compat) ->
                                             let uu____84078 =
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
                                                   let uu____84101 =
                                                     term_as_mlexpr env w  in
                                                   (match uu____84101 with
                                                    | (w1,f_w,t_w) ->
                                                        let w2 =
                                                          maybe_coerce w_pos
                                                            env w1 t_w
                                                            FStar_Extraction_ML_Syntax.ml_bool_ty
                                                           in
                                                        ((FStar_Pervasives_Native.Some
                                                            w2), f_w))
                                                in
                                             (match uu____84078 with
                                              | (when_opt1,f_when) ->
                                                  let uu____84151 =
                                                    term_as_mlexpr env
                                                      branch1
                                                     in
                                                  (match uu____84151 with
                                                   | (mlbranch,f_branch,t_branch)
                                                       ->
                                                       let uu____84186 =
                                                         FStar_All.pipe_right
                                                           p
                                                           (FStar_List.map
                                                              (fun
                                                                 uu____84263 
                                                                 ->
                                                                 match uu____84263
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
                                                         uu____84186)))))
                               true)
                           in
                        match uu____83872 with
                        | (pat_t_compat,mlbranches) ->
                            let mlbranches1 = FStar_List.flatten mlbranches
                               in
                            let e1 =
                              if pat_t_compat
                              then e
                              else
                                (FStar_Extraction_ML_UEnv.debug g
                                   (fun uu____84434  ->
                                      let uu____84435 =
                                        FStar_Extraction_ML_Code.string_of_mlexpr
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          e
                                         in
                                      let uu____84437 =
                                        FStar_Extraction_ML_Code.string_of_mlty
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          t_e
                                         in
                                      FStar_Util.print2
                                        "Coercing scrutinee %s from type %s because pattern type is incompatible\n"
                                        uu____84435 uu____84437);
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty t_e)
                                   (FStar_Extraction_ML_Syntax.MLE_Coerce
                                      (e, t_e,
                                        FStar_Extraction_ML_Syntax.MLTY_Top)))
                               in
                            (match mlbranches1 with
                             | [] ->
                                 let uu____84464 =
                                   let uu____84465 =
                                     FStar_Syntax_Syntax.lid_as_fv
                                       FStar_Parser_Const.failwith_lid
                                       FStar_Syntax_Syntax.delta_constant
                                       FStar_Pervasives_Native.None
                                      in
                                   FStar_Extraction_ML_UEnv.lookup_fv g
                                     uu____84465
                                    in
                                 (match uu____84464 with
                                  | {
                                      FStar_Extraction_ML_UEnv.exp_b_name =
                                        uu____84472;
                                      FStar_Extraction_ML_UEnv.exp_b_expr =
                                        fw;
                                      FStar_Extraction_ML_UEnv.exp_b_tscheme
                                        = uu____84474;
                                      FStar_Extraction_ML_UEnv.exp_b_inst_ok
                                        = uu____84475;_}
                                      ->
                                      let uu____84478 =
                                        let uu____84479 =
                                          let uu____84480 =
                                            let uu____84487 =
                                              let uu____84490 =
                                                FStar_All.pipe_left
                                                  (FStar_Extraction_ML_Syntax.with_ty
                                                     FStar_Extraction_ML_Syntax.ml_string_ty)
                                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                                     (FStar_Extraction_ML_Syntax.MLC_String
                                                        "unreachable"))
                                                 in
                                              [uu____84490]  in
                                            (fw, uu____84487)  in
                                          FStar_Extraction_ML_Syntax.MLE_App
                                            uu____84480
                                           in
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             FStar_Extraction_ML_Syntax.ml_int_ty)
                                          uu____84479
                                         in
                                      (uu____84478,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        FStar_Extraction_ML_Syntax.ml_int_ty))
                             | (uu____84494,uu____84495,(uu____84496,f_first,t_first))::rest
                                 ->
                                 let uu____84556 =
                                   FStar_List.fold_left
                                     (fun uu____84598  ->
                                        fun uu____84599  ->
                                          match (uu____84598, uu____84599)
                                          with
                                          | ((topt,f),(uu____84656,uu____84657,
                                                       (uu____84658,f_branch,t_branch)))
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
                                                    let uu____84714 =
                                                      type_leq g t1 t_branch
                                                       in
                                                    if uu____84714
                                                    then
                                                      FStar_Pervasives_Native.Some
                                                        t_branch
                                                    else
                                                      (let uu____84721 =
                                                         type_leq g t_branch
                                                           t1
                                                          in
                                                       if uu____84721
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
                                 (match uu____84556 with
                                  | (topt,f_match) ->
                                      let mlbranches2 =
                                        FStar_All.pipe_right mlbranches1
                                          (FStar_List.map
                                             (fun uu____84819  ->
                                                match uu____84819 with
                                                | (p,(wopt,uu____84848),
                                                   (b1,uu____84850,t1)) ->
                                                    let b2 =
                                                      match topt with
                                                      | FStar_Pervasives_Native.None
                                                           ->
                                                          FStar_Extraction_ML_Syntax.apply_obj_repr
                                                            b1 t1
                                                      | FStar_Pervasives_Native.Some
                                                          uu____84869 -> b1
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
                                      let uu____84874 =
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             t_match)
                                          (FStar_Extraction_ML_Syntax.MLE_Match
                                             (e1, mlbranches2))
                                         in
                                      (uu____84874, f_match, t_match)))))))

let (ind_discriminator_body :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlmodule1)
  =
  fun env  ->
    fun discName  ->
      fun constrName  ->
        let uu____84901 =
          let uu____84906 =
            FStar_TypeChecker_Env.lookup_lid
              env.FStar_Extraction_ML_UEnv.env_tcenv discName
             in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____84906  in
        match uu____84901 with
        | (uu____84931,fstar_disc_type) ->
            let wildcards =
              let uu____84941 =
                let uu____84942 = FStar_Syntax_Subst.compress fstar_disc_type
                   in
                uu____84942.FStar_Syntax_Syntax.n  in
              match uu____84941 with
              | FStar_Syntax_Syntax.Tm_arrow (binders,uu____84953) ->
                  let uu____84974 =
                    FStar_All.pipe_right binders
                      (FStar_List.filter
                         (fun uu___620_85008  ->
                            match uu___620_85008 with
                            | (uu____85016,FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____85017)) ->
                                true
                            | uu____85022 -> false))
                     in
                  FStar_All.pipe_right uu____84974
                    (FStar_List.map
                       (fun uu____85058  ->
                          let uu____85065 = fresh "_"  in
                          (uu____85065, FStar_Extraction_ML_Syntax.MLTY_Top)))
              | uu____85069 -> failwith "Discriminator must be a function"
               in
            let mlid = fresh "_discr_"  in
            let targ = FStar_Extraction_ML_Syntax.MLTY_Top  in
            let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top  in
            let discrBody =
              let uu____85084 =
                let uu____85085 =
                  let uu____85097 =
                    let uu____85098 =
                      let uu____85099 =
                        let uu____85114 =
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty targ)
                            (FStar_Extraction_ML_Syntax.MLE_Name ([], mlid))
                           in
                        let uu____85120 =
                          let uu____85131 =
                            let uu____85140 =
                              let uu____85141 =
                                let uu____85148 =
                                  FStar_Extraction_ML_Syntax.mlpath_of_lident
                                    constrName
                                   in
                                (uu____85148,
                                  [FStar_Extraction_ML_Syntax.MLP_Wild])
                                 in
                              FStar_Extraction_ML_Syntax.MLP_CTor uu____85141
                               in
                            let uu____85151 =
                              FStar_All.pipe_left
                                (FStar_Extraction_ML_Syntax.with_ty
                                   FStar_Extraction_ML_Syntax.ml_bool_ty)
                                (FStar_Extraction_ML_Syntax.MLE_Const
                                   (FStar_Extraction_ML_Syntax.MLC_Bool true))
                               in
                            (uu____85140, FStar_Pervasives_Native.None,
                              uu____85151)
                             in
                          let uu____85155 =
                            let uu____85166 =
                              let uu____85175 =
                                FStar_All.pipe_left
                                  (FStar_Extraction_ML_Syntax.with_ty
                                     FStar_Extraction_ML_Syntax.ml_bool_ty)
                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                     (FStar_Extraction_ML_Syntax.MLC_Bool
                                        false))
                                 in
                              (FStar_Extraction_ML_Syntax.MLP_Wild,
                                FStar_Pervasives_Native.None, uu____85175)
                               in
                            [uu____85166]  in
                          uu____85131 :: uu____85155  in
                        (uu____85114, uu____85120)  in
                      FStar_Extraction_ML_Syntax.MLE_Match uu____85099  in
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.ml_bool_ty) uu____85098
                     in
                  ((FStar_List.append wildcards [(mlid, targ)]), uu____85097)
                   in
                FStar_Extraction_ML_Syntax.MLE_Fun uu____85085  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty disc_ty) uu____85084
               in
            let uu____85236 =
              let uu____85237 =
                let uu____85240 =
                  let uu____85241 =
                    FStar_Extraction_ML_UEnv.convIdent
                      discName.FStar_Ident.ident
                     in
                  {
                    FStar_Extraction_ML_Syntax.mllb_name = uu____85241;
                    FStar_Extraction_ML_Syntax.mllb_tysc =
                      FStar_Pervasives_Native.None;
                    FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                    FStar_Extraction_ML_Syntax.mllb_def = discrBody;
                    FStar_Extraction_ML_Syntax.mllb_meta = [];
                    FStar_Extraction_ML_Syntax.print_typ = false
                  }  in
                [uu____85240]  in
              (FStar_Extraction_ML_Syntax.NonRec, uu____85237)  in
            FStar_Extraction_ML_Syntax.MLM_Let uu____85236
  