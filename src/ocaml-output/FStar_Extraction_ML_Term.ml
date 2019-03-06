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
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let topt =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant]
              env.FStar_Extraction_ML_UEnv.env_tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match topt with
           | FStar_Pervasives_Native.None  -> false
           | FStar_Pervasives_Native.Some (uu____71440,t2) -> is_arity env t2)
      | FStar_Syntax_Syntax.Tm_app uu____71446 ->
          let uu____71463 = FStar_Syntax_Util.head_and_args t1  in
          (match uu____71463 with | (head1,uu____71482) -> is_arity env head1)
      | FStar_Syntax_Syntax.Tm_uinst (head1,uu____71508) ->
          is_arity env head1
      | FStar_Syntax_Syntax.Tm_refine (x,uu____71514) ->
          is_arity env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_abs (uu____71519,body,uu____71521) ->
          is_arity env body
      | FStar_Syntax_Syntax.Tm_let (uu____71546,body) -> is_arity env body
      | FStar_Syntax_Syntax.Tm_match (uu____71566,branches) ->
          (match branches with
           | (uu____71605,uu____71606,e)::uu____71608 -> is_arity env e
           | uu____71655 -> false)
  
let rec (is_type_aux :
  FStar_Extraction_ML_UEnv.uenv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____71687 ->
          let uu____71710 =
            let uu____71712 = FStar_Syntax_Print.tag_of_term t1  in
            FStar_Util.format1 "Impossible: %s" uu____71712  in
          failwith uu____71710
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____71716 =
            let uu____71718 = FStar_Syntax_Print.tag_of_term t1  in
            FStar_Util.format1 "Impossible: %s" uu____71718  in
          failwith uu____71716
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____71723 = FStar_Syntax_Util.unfold_lazy i  in
          is_type_aux env uu____71723
      | FStar_Syntax_Syntax.Tm_constant uu____71724 -> false
      | FStar_Syntax_Syntax.Tm_type uu____71726 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____71728 -> true
      | FStar_Syntax_Syntax.Tm_arrow uu____71736 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.failwith_lid ->
          false
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Extraction_ML_UEnv.is_type_name env fv
      | FStar_Syntax_Syntax.Tm_uvar
          ({ FStar_Syntax_Syntax.ctx_uvar_head = uu____71755;
             FStar_Syntax_Syntax.ctx_uvar_gamma = uu____71756;
             FStar_Syntax_Syntax.ctx_uvar_binders = uu____71757;
             FStar_Syntax_Syntax.ctx_uvar_typ = t2;
             FStar_Syntax_Syntax.ctx_uvar_reason = uu____71759;
             FStar_Syntax_Syntax.ctx_uvar_should_check = uu____71760;
             FStar_Syntax_Syntax.ctx_uvar_range = uu____71761;
             FStar_Syntax_Syntax.ctx_uvar_meta = uu____71762;_},s)
          ->
          let uu____71811 = FStar_Syntax_Subst.subst' s t2  in
          is_arity env uu____71811
      | FStar_Syntax_Syntax.Tm_bvar
          { FStar_Syntax_Syntax.ppname = uu____71812;
            FStar_Syntax_Syntax.index = uu____71813;
            FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_name
          { FStar_Syntax_Syntax.ppname = uu____71818;
            FStar_Syntax_Syntax.index = uu____71819;
            FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____71825,uu____71826) ->
          is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____71868) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____71875) ->
          let uu____71900 = FStar_Syntax_Subst.open_term bs body  in
          (match uu____71900 with
           | (uu____71906,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
          let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
          let uu____71926 =
            let uu____71931 =
              let uu____71932 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____71932]  in
            FStar_Syntax_Subst.open_term uu____71931 body  in
          (match uu____71926 with
           | (uu____71952,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_let ((uu____71954,lbs),body) ->
          let uu____71974 = FStar_Syntax_Subst.open_let_rec lbs body  in
          (match uu____71974 with
           | (uu____71982,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_match (uu____71988,branches) ->
          (match branches with
           | b::uu____72028 ->
               let uu____72073 = FStar_Syntax_Subst.open_branch b  in
               (match uu____72073 with
                | (uu____72075,uu____72076,e) -> is_type_aux env e)
           | uu____72094 -> false)
      | FStar_Syntax_Syntax.Tm_quoted uu____72112 -> false
      | FStar_Syntax_Syntax.Tm_meta (t2,uu____72121) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_app (head1,uu____72127) ->
          is_type_aux env head1
  
let (is_type :
  FStar_Extraction_ML_UEnv.uenv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      FStar_Extraction_ML_UEnv.debug env
        (fun uu____72168  ->
           let uu____72169 = FStar_Syntax_Print.tag_of_term t  in
           let uu____72171 = FStar_Syntax_Print.term_to_string t  in
           FStar_Util.print2 "checking is_type (%s) %s\n" uu____72169
             uu____72171);
      (let b = is_type_aux env t  in
       FStar_Extraction_ML_UEnv.debug env
         (fun uu____72180  ->
            if b
            then
              let uu____72182 = FStar_Syntax_Print.term_to_string t  in
              let uu____72184 = FStar_Syntax_Print.tag_of_term t  in
              FStar_Util.print2 "yes, is_type %s (%s)\n" uu____72182
                uu____72184
            else
              (let uu____72189 = FStar_Syntax_Print.term_to_string t  in
               let uu____72191 = FStar_Syntax_Print.tag_of_term t  in
               FStar_Util.print2 "not a type %s (%s)\n" uu____72189
                 uu____72191));
       b)
  
let is_type_binder :
  'Auu____72201 .
    FStar_Extraction_ML_UEnv.uenv ->
      (FStar_Syntax_Syntax.bv * 'Auu____72201) -> Prims.bool
  =
  fun env  ->
    fun x  ->
      is_arity env (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
  
let (is_constructor : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____72228 =
      let uu____72229 = FStar_Syntax_Subst.compress t  in
      uu____72229.FStar_Syntax_Syntax.n  in
    match uu____72228 with
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____72233;
          FStar_Syntax_Syntax.fv_delta = uu____72234;
          FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
            (FStar_Syntax_Syntax.Data_ctor );_}
        -> true
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____72236;
          FStar_Syntax_Syntax.fv_delta = uu____72237;
          FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
            (FStar_Syntax_Syntax.Record_ctor uu____72238);_}
        -> true
    | uu____72246 -> false
  
let rec (is_fstar_value : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____72255 =
      let uu____72256 = FStar_Syntax_Subst.compress t  in
      uu____72256.FStar_Syntax_Syntax.n  in
    match uu____72255 with
    | FStar_Syntax_Syntax.Tm_constant uu____72260 -> true
    | FStar_Syntax_Syntax.Tm_bvar uu____72262 -> true
    | FStar_Syntax_Syntax.Tm_fvar uu____72264 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____72266 -> true
    | FStar_Syntax_Syntax.Tm_app (head1,args) ->
        let uu____72312 = is_constructor head1  in
        if uu____72312
        then
          FStar_All.pipe_right args
            (FStar_List.for_all
               (fun uu____72334  ->
                  match uu____72334 with
                  | (te,uu____72343) -> is_fstar_value te))
        else false
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____72352) -> is_fstar_value t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____72358,uu____72359) ->
        is_fstar_value t1
    | uu____72400 -> false
  
let rec (is_ml_value : FStar_Extraction_ML_Syntax.mlexpr -> Prims.bool) =
  fun e  ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_Const uu____72410 -> true
    | FStar_Extraction_ML_Syntax.MLE_Var uu____72412 -> true
    | FStar_Extraction_ML_Syntax.MLE_Name uu____72415 -> true
    | FStar_Extraction_ML_Syntax.MLE_Fun uu____72417 -> true
    | FStar_Extraction_ML_Syntax.MLE_CTor (uu____72430,exps) ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Tuple exps ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Record (uu____72439,fields) ->
        FStar_Util.for_all
          (fun uu____72469  ->
             match uu____72469 with | (uu____72476,e1) -> is_ml_value e1)
          fields
    | FStar_Extraction_ML_Syntax.MLE_TApp (h,uu____72481) -> is_ml_value h
    | uu____72486 -> false
  
let (fresh : Prims.string -> Prims.string) =
  let c = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun x  ->
    FStar_Util.incr c;
    (let uu____72537 =
       let uu____72539 = FStar_ST.op_Bang c  in
       FStar_Util.string_of_int uu____72539  in
     Prims.op_Hat x uu____72537)
  
let (normalize_abs : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t0  ->
    let rec aux bs t copt =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_abs (bs',body,copt1) ->
          aux (FStar_List.append bs bs') body copt1
      | uu____72664 ->
          let e' = FStar_Syntax_Util.unascribe t1  in
          let uu____72666 = FStar_Syntax_Util.is_fun e'  in
          if uu____72666
          then aux bs e' copt
          else FStar_Syntax_Util.abs bs e' copt
       in
    aux [] t0 FStar_Pervasives_Native.None
  
let (unit_binder : FStar_Syntax_Syntax.binder) =
  let uu____72680 =
    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
      FStar_Syntax_Syntax.t_unit
     in
  FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____72680 
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
      (let uu____72771 = FStar_List.hd l  in
       match uu____72771 with
       | (p1,w1,e1) ->
           let uu____72806 =
             let uu____72815 = FStar_List.tl l  in FStar_List.hd uu____72815
              in
           (match uu____72806 with
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
                 | uu____72899 -> def)))
  
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
      let uu____72938 = FStar_Extraction_ML_Util.doms_and_cod t  in
      match uu____72938 with
      | (ts,r) ->
          if ts = []
          then e
          else
            (let vs = FStar_List.map (fun uu____72962  -> fresh "a") ts  in
             let vs_ts = FStar_List.zip vs ts  in
             let vs_es =
               let uu____72976 = FStar_List.zip vs ts  in
               FStar_List.map
                 (fun uu____72993  ->
                    match uu____72993 with
                    | (v1,t1) ->
                        FStar_Extraction_ML_Syntax.with_ty t1
                          (FStar_Extraction_ML_Syntax.MLE_Var v1))
                 uu____72976
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
      let uu____73024 = FStar_Extraction_ML_Util.doms_and_cod t  in
      match uu____73024 with
      | (ts,r) ->
          let body r1 =
            let r2 =
              let uu____73044 = FStar_Extraction_ML_Util.udelta_unfold g r1
                 in
              match uu____73044 with
              | FStar_Pervasives_Native.None  -> r1
              | FStar_Pervasives_Native.Some r2 -> r2  in
            match r2 with
            | FStar_Extraction_ML_Syntax.MLTY_Erased  ->
                FStar_Extraction_ML_Syntax.ml_unit
            | FStar_Extraction_ML_Syntax.MLTY_Top  ->
                FStar_Extraction_ML_Syntax.apply_obj_repr
                  FStar_Extraction_ML_Syntax.ml_unit
                  FStar_Extraction_ML_Syntax.MLTY_Erased
            | uu____73048 ->
                FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty r2)
                  (FStar_Extraction_ML_Syntax.MLE_Coerce
                     (FStar_Extraction_ML_Syntax.ml_unit,
                       FStar_Extraction_ML_Syntax.MLTY_Erased, r2))
             in
          if ts = []
          then body r
          else
            (let vs = FStar_List.map (fun uu____73060  -> fresh "a") ts  in
             let vs_ts = FStar_List.zip vs ts  in
             let uu____73071 =
               let uu____73072 =
                 let uu____73084 = body r  in (vs_ts, uu____73084)  in
               FStar_Extraction_ML_Syntax.MLE_Fun uu____73072  in
             FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t)
               uu____73071)
  
let (maybe_eta_expand :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun expect  ->
    fun e  ->
      let uu____73103 =
        (FStar_Options.ml_no_eta_expand_coertions ()) ||
          (let uu____73106 = FStar_Options.codegen ()  in
           uu____73106 = (FStar_Pervasives_Native.Some FStar_Options.Kremlin))
         in
      if uu____73103 then e else eta_expand expect e
  
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
            | uu____73184 ->
                FStar_Extraction_ML_Syntax.MLE_Fun ([binder], body)
             in
          let rec aux e1 ty1 expect1 =
            let coerce_branch uu____73239 =
              match uu____73239 with
              | (pat,w,b) ->
                  let uu____73263 = aux b ty1 expect1  in
                  (pat, w, uu____73263)
               in
            match ((e1.FStar_Extraction_ML_Syntax.expr), ty1, expect1) with
            | (FStar_Extraction_ML_Syntax.MLE_Fun
               (arg::rest,body),FStar_Extraction_ML_Syntax.MLTY_Fun
               (t0,uu____73270,t1),FStar_Extraction_ML_Syntax.MLTY_Fun
               (s0,uu____73273,s1)) ->
                let body1 =
                  match rest with
                  | [] -> body
                  | uu____73305 ->
                      FStar_Extraction_ML_Syntax.with_ty t1
                        (FStar_Extraction_ML_Syntax.MLE_Fun (rest, body))
                   in
                let body2 = aux body1 t1 s1  in
                let uu____73321 = type_leq g s0 t0  in
                if uu____73321
                then
                  FStar_Extraction_ML_Syntax.with_ty expect1
                    (mk_fun arg body2)
                else
                  (let lb =
                     let uu____73327 =
                       let uu____73328 =
                         let uu____73329 =
                           let uu____73336 =
                             FStar_All.pipe_left
                               (FStar_Extraction_ML_Syntax.with_ty s0)
                               (FStar_Extraction_ML_Syntax.MLE_Var
                                  (FStar_Pervasives_Native.fst arg))
                              in
                           (uu____73336, s0, t0)  in
                         FStar_Extraction_ML_Syntax.MLE_Coerce uu____73329
                          in
                       FStar_Extraction_ML_Syntax.with_ty t0 uu____73328  in
                     {
                       FStar_Extraction_ML_Syntax.mllb_name =
                         (FStar_Pervasives_Native.fst arg);
                       FStar_Extraction_ML_Syntax.mllb_tysc =
                         (FStar_Pervasives_Native.Some ([], t0));
                       FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                       FStar_Extraction_ML_Syntax.mllb_def = uu____73327;
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
               (lbs,body),uu____73355,uu____73356) ->
                let uu____73369 =
                  let uu____73370 =
                    let uu____73381 = aux body ty1 expect1  in
                    (lbs, uu____73381)  in
                  FStar_Extraction_ML_Syntax.MLE_Let uu____73370  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____73369
            | (FStar_Extraction_ML_Syntax.MLE_Match
               (s,branches),uu____73390,uu____73391) ->
                let uu____73412 =
                  let uu____73413 =
                    let uu____73428 = FStar_List.map coerce_branch branches
                       in
                    (s, uu____73428)  in
                  FStar_Extraction_ML_Syntax.MLE_Match uu____73413  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____73412
            | (FStar_Extraction_ML_Syntax.MLE_If
               (s,b1,b2_opt),uu____73468,uu____73469) ->
                let uu____73474 =
                  let uu____73475 =
                    let uu____73484 = aux b1 ty1 expect1  in
                    let uu____73485 =
                      FStar_Util.map_opt b2_opt
                        (fun b2  -> aux b2 ty1 expect1)
                       in
                    (s, uu____73484, uu____73485)  in
                  FStar_Extraction_ML_Syntax.MLE_If uu____73475  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____73474
            | (FStar_Extraction_ML_Syntax.MLE_Seq es,uu____73493,uu____73494)
                ->
                let uu____73497 = FStar_Util.prefix es  in
                (match uu____73497 with
                 | (prefix1,last1) ->
                     let uu____73510 =
                       let uu____73511 =
                         let uu____73514 =
                           let uu____73517 = aux last1 ty1 expect1  in
                           [uu____73517]  in
                         FStar_List.append prefix1 uu____73514  in
                       FStar_Extraction_ML_Syntax.MLE_Seq uu____73511  in
                     FStar_All.pipe_left
                       (FStar_Extraction_ML_Syntax.with_ty expect1)
                       uu____73510)
            | (FStar_Extraction_ML_Syntax.MLE_Try
               (s,branches),uu____73520,uu____73521) ->
                let uu____73542 =
                  let uu____73543 =
                    let uu____73558 = FStar_List.map coerce_branch branches
                       in
                    (s, uu____73558)  in
                  FStar_Extraction_ML_Syntax.MLE_Try uu____73543  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____73542
            | uu____73595 ->
                FStar_Extraction_ML_Syntax.with_ty expect1
                  (FStar_Extraction_ML_Syntax.MLE_Coerce (e1, ty1, expect1))
             in
          aux e ty expect
  
let maybe_coerce :
  'Auu____73615 .
    'Auu____73615 ->
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
            let uu____73642 =
              type_leq_c g (FStar_Pervasives_Native.Some e) ty1 expect  in
            match uu____73642 with
            | (true ,FStar_Pervasives_Native.Some e') -> e'
            | uu____73655 ->
                (match ty1 with
                 | FStar_Extraction_ML_Syntax.MLTY_Erased  ->
                     default_value_for_ty g expect
                 | uu____73663 ->
                     let uu____73664 =
                       let uu____73666 =
                         FStar_Extraction_ML_Util.erase_effect_annotations
                           ty1
                          in
                       let uu____73667 =
                         FStar_Extraction_ML_Util.erase_effect_annotations
                           expect
                          in
                       type_leq g uu____73666 uu____73667  in
                     if uu____73664
                     then
                       (FStar_Extraction_ML_UEnv.debug g
                          (fun uu____73673  ->
                             let uu____73674 =
                               FStar_Extraction_ML_Code.string_of_mlexpr
                                 g.FStar_Extraction_ML_UEnv.currentModule e
                                in
                             let uu____73676 =
                               FStar_Extraction_ML_Code.string_of_mlty
                                 g.FStar_Extraction_ML_UEnv.currentModule ty1
                                in
                             FStar_Util.print2
                               "\n Effect mismatch on type of %s : %s\n"
                               uu____73674 uu____73676);
                        e)
                     else
                       (FStar_Extraction_ML_UEnv.debug g
                          (fun uu____73686  ->
                             let uu____73687 =
                               FStar_Extraction_ML_Code.string_of_mlexpr
                                 g.FStar_Extraction_ML_UEnv.currentModule e
                                in
                             let uu____73689 =
                               FStar_Extraction_ML_Code.string_of_mlty
                                 g.FStar_Extraction_ML_UEnv.currentModule ty1
                                in
                             let uu____73691 =
                               FStar_Extraction_ML_Code.string_of_mlty
                                 g.FStar_Extraction_ML_UEnv.currentModule
                                 expect
                                in
                             FStar_Util.print3
                               "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n"
                               uu____73687 uu____73689 uu____73691);
                        (let uu____73694 = apply_coercion g e ty1 expect  in
                         maybe_eta_expand expect uu____73694)))
  
let (bv_as_mlty :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun bv  ->
      let uu____73706 = FStar_Extraction_ML_UEnv.lookup_bv g bv  in
      match uu____73706 with
      | FStar_Util.Inl ty_b -> ty_b.FStar_Extraction_ML_UEnv.ty_b_ty
      | uu____73708 -> FStar_Extraction_ML_Syntax.MLTY_Top
  
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
    | FStar_Syntax_Syntax.Total uu____73726 -> c
    | FStar_Syntax_Syntax.GTotal uu____73735 -> c
    | FStar_Syntax_Syntax.Comp ct ->
        let effect_args =
          FStar_List.map
            (fun uu____73771  ->
               match uu____73771 with
               | (uu____73786,aq) -> (FStar_Syntax_Syntax.t_unit, aq))
            ct.FStar_Syntax_Syntax.effect_args
           in
        let ct1 =
          let uu___1131_73799 = ct  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___1131_73799.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___1131_73799.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ =
              (uu___1131_73799.FStar_Syntax_Syntax.result_typ);
            FStar_Syntax_Syntax.effect_args = effect_args;
            FStar_Syntax_Syntax.flags =
              (uu___1131_73799.FStar_Syntax_Syntax.flags)
          }  in
        let c1 =
          let uu___1134_73803 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
            FStar_Syntax_Syntax.pos =
              (uu___1134_73803.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___1134_73803.FStar_Syntax_Syntax.vars)
          }  in
        c1
  
let rec (translate_term_to_mlty :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun t0  ->
      let arg_as_mlty g1 uu____73852 =
        match uu____73852 with
        | (a,uu____73860) ->
            let uu____73865 = is_type g1 a  in
            if uu____73865
            then translate_term_to_mlty g1 a
            else FStar_Extraction_ML_UEnv.erasedContent
         in
      let fv_app_as_mlty g1 fv args =
        let uu____73886 =
          let uu____73888 = FStar_Extraction_ML_UEnv.is_fv_type g1 fv  in
          Prims.op_Negation uu____73888  in
        if uu____73886
        then FStar_Extraction_ML_Syntax.MLTY_Top
        else
          (let uu____73893 =
             let uu____73908 =
               FStar_TypeChecker_Env.lookup_lid
                 g1.FStar_Extraction_ML_UEnv.env_tcenv
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             match uu____73908 with
             | ((uu____73931,fvty),uu____73933) ->
                 let fvty1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Env.UnfoldUntil
                        FStar_Syntax_Syntax.delta_constant]
                     g1.FStar_Extraction_ML_UEnv.env_tcenv fvty
                    in
                 FStar_Syntax_Util.arrow_formals fvty1
              in
           match uu____73893 with
           | (formals,uu____73940) ->
               let mlargs = FStar_List.map (arg_as_mlty g1) args  in
               let mlargs1 =
                 let n_args = FStar_List.length args  in
                 if (FStar_List.length formals) > n_args
                 then
                   let uu____73997 = FStar_Util.first_N n_args formals  in
                   match uu____73997 with
                   | (uu____74030,rest) ->
                       let uu____74064 =
                         FStar_List.map
                           (fun uu____74074  ->
                              FStar_Extraction_ML_UEnv.erasedContent) rest
                          in
                       FStar_List.append mlargs uu____74064
                 else mlargs  in
               let nm =
                 let uu____74084 =
                   FStar_Extraction_ML_UEnv.maybe_mangle_type_projector g1 fv
                    in
                 match uu____74084 with
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
        | FStar_Syntax_Syntax.Tm_type uu____74102 ->
            FStar_Extraction_ML_Syntax.MLTY_Erased
        | FStar_Syntax_Syntax.Tm_bvar uu____74103 ->
            let uu____74104 =
              let uu____74106 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____74106
               in
            failwith uu____74104
        | FStar_Syntax_Syntax.Tm_delayed uu____74109 ->
            let uu____74132 =
              let uu____74134 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____74134
               in
            failwith uu____74132
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____74137 =
              let uu____74139 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____74139
               in
            failwith uu____74137
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____74143 = FStar_Syntax_Util.unfold_lazy i  in
            translate_term_to_mlty env uu____74143
        | FStar_Syntax_Syntax.Tm_constant uu____74144 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_quoted uu____74145 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_uvar uu____74152 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_meta (t2,uu____74166) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____74171;
               FStar_Syntax_Syntax.index = uu____74172;
               FStar_Syntax_Syntax.sort = t2;_},uu____74174)
            -> translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_uinst (t2,uu____74183) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____74189,uu____74190) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
        | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv []
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let uu____74263 = FStar_Syntax_Subst.open_comp bs c  in
            (match uu____74263 with
             | (bs1,c1) ->
                 let uu____74270 = binders_as_ml_binders env bs1  in
                 (match uu____74270 with
                  | (mlbs,env1) ->
                      let t_ret =
                        let eff =
                          FStar_TypeChecker_Env.norm_eff_name
                            env1.FStar_Extraction_ML_UEnv.env_tcenv
                            (FStar_Syntax_Util.comp_effect_name c1)
                           in
                        let c2 = comp_no_args c1  in
                        let uu____74303 =
                          let uu____74310 =
                            FStar_TypeChecker_Env.effect_decl_opt
                              env1.FStar_Extraction_ML_UEnv.env_tcenv eff
                             in
                          FStar_Util.must uu____74310  in
                        match uu____74303 with
                        | (ed,qualifiers) ->
                            let uu____74331 =
                              FStar_TypeChecker_Env.is_reifiable_effect
                                g.FStar_Extraction_ML_UEnv.env_tcenv
                                ed.FStar_Syntax_Syntax.mname
                               in
                            if uu____74331
                            then
                              let t2 =
                                FStar_TypeChecker_Env.reify_comp
                                  env1.FStar_Extraction_ML_UEnv.env_tcenv c2
                                  FStar_Syntax_Syntax.U_unknown
                                 in
                              (FStar_Extraction_ML_UEnv.debug env1
                                 (fun uu____74339  ->
                                    let uu____74340 =
                                      FStar_Syntax_Print.comp_to_string c2
                                       in
                                    let uu____74342 =
                                      FStar_Syntax_Print.term_to_string t2
                                       in
                                    FStar_Util.print2
                                      "Translating comp type %s as %s\n"
                                      uu____74340 uu____74342);
                               (let res = translate_term_to_mlty env1 t2  in
                                FStar_Extraction_ML_UEnv.debug env1
                                  (fun uu____74351  ->
                                     let uu____74352 =
                                       FStar_Syntax_Print.comp_to_string c2
                                        in
                                     let uu____74354 =
                                       FStar_Syntax_Print.term_to_string t2
                                        in
                                     let uu____74356 =
                                       FStar_Extraction_ML_Code.string_of_mlty
                                         env1.FStar_Extraction_ML_UEnv.currentModule
                                         res
                                        in
                                     FStar_Util.print3
                                       "Translated comp type %s as %s ... to %s\n"
                                       uu____74352 uu____74354 uu____74356);
                                res))
                            else
                              translate_term_to_mlty env1
                                (FStar_Syntax_Util.comp_result c2)
                         in
                      let erase =
                        effect_as_etag env1
                          (FStar_Syntax_Util.comp_effect_name c1)
                         in
                      let uu____74362 =
                        FStar_List.fold_right
                          (fun uu____74382  ->
                             fun uu____74383  ->
                               match (uu____74382, uu____74383) with
                               | ((uu____74406,t2),(tag,t')) ->
                                   (FStar_Extraction_ML_Syntax.E_PURE,
                                     (FStar_Extraction_ML_Syntax.MLTY_Fun
                                        (t2, tag, t')))) mlbs (erase, t_ret)
                         in
                      (match uu____74362 with | (uu____74421,t2) -> t2)))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let res =
              let uu____74450 =
                let uu____74451 = FStar_Syntax_Util.un_uinst head1  in
                uu____74451.FStar_Syntax_Syntax.n  in
              match uu____74450 with
              | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv args
              | FStar_Syntax_Syntax.Tm_app (head2,args') ->
                  let uu____74482 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_app
                         (head2, (FStar_List.append args' args)))
                      FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                     in
                  translate_term_to_mlty env uu____74482
              | uu____74503 -> FStar_Extraction_ML_UEnv.unknownType  in
            res
        | FStar_Syntax_Syntax.Tm_abs (bs,ty,uu____74506) ->
            let uu____74531 = FStar_Syntax_Subst.open_term bs ty  in
            (match uu____74531 with
             | (bs1,ty1) ->
                 let uu____74538 = binders_as_ml_binders env bs1  in
                 (match uu____74538 with
                  | (bts,env1) -> translate_term_to_mlty env1 ty1))
        | FStar_Syntax_Syntax.Tm_let uu____74566 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_match uu____74580 ->
            FStar_Extraction_ML_UEnv.unknownType
         in
      let rec is_top_ty t =
        match t with
        | FStar_Extraction_ML_Syntax.MLTY_Top  -> true
        | FStar_Extraction_ML_Syntax.MLTY_Named uu____74612 ->
            let uu____74619 = FStar_Extraction_ML_Util.udelta_unfold g t  in
            (match uu____74619 with
             | FStar_Pervasives_Native.None  -> false
             | FStar_Pervasives_Native.Some t1 -> is_top_ty t1)
        | uu____74625 -> false  in
      let uu____74627 =
        FStar_TypeChecker_Util.must_erase_for_extraction
          g.FStar_Extraction_ML_UEnv.env_tcenv t0
         in
      if uu____74627
      then FStar_Extraction_ML_Syntax.MLTY_Erased
      else
        (let mlt = aux g t0  in
         let uu____74633 = is_top_ty mlt  in
         if uu____74633 then FStar_Extraction_ML_Syntax.MLTY_Top else mlt)

and (binders_as_ml_binders :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.binders ->
      ((FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)
        Prims.list * FStar_Extraction_ML_UEnv.uenv))
  =
  fun g  ->
    fun bs  ->
      let uu____74651 =
        FStar_All.pipe_right bs
          (FStar_List.fold_left
             (fun uu____74707  ->
                fun b  ->
                  match uu____74707 with
                  | (ml_bs,env) ->
                      let uu____74753 = is_type_binder g b  in
                      if uu____74753
                      then
                        let b1 = FStar_Pervasives_Native.fst b  in
                        let env1 =
                          FStar_Extraction_ML_UEnv.extend_ty env b1
                            (FStar_Pervasives_Native.Some
                               FStar_Extraction_ML_Syntax.MLTY_Top)
                           in
                        let ml_b =
                          let uu____74779 =
                            FStar_Extraction_ML_UEnv.bv_as_ml_termvar b1  in
                          (uu____74779,
                            FStar_Extraction_ML_Syntax.ml_unit_ty)
                           in
                        ((ml_b :: ml_bs), env1)
                      else
                        (let b1 = FStar_Pervasives_Native.fst b  in
                         let t =
                           translate_term_to_mlty env
                             b1.FStar_Syntax_Syntax.sort
                            in
                         let uu____74800 =
                           FStar_Extraction_ML_UEnv.extend_bv env b1 
                             ([], t) false false false
                            in
                         match uu____74800 with
                         | (env1,b2,uu____74825) ->
                             let ml_b =
                               let uu____74834 =
                                 FStar_Extraction_ML_UEnv.removeTick b2  in
                               (uu____74834, t)  in
                             ((ml_b :: ml_bs), env1))) ([], g))
         in
      match uu____74651 with | (ml_bs,env) -> ((FStar_List.rev ml_bs), env)

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
      | (FStar_Extraction_ML_Syntax.MLE_Seq es1,uu____74930) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (FStar_List.append es1 [e2])
      | (uu____74933,FStar_Extraction_ML_Syntax.MLE_Seq es2) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (e1 :: es2)
      | uu____74937 -> FStar_Extraction_ML_Syntax.MLE_Seq [e1; e2]
  
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
                    | uu____74971 when
                        (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
                          =
                          FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr
                        -> body.FStar_Extraction_ML_Syntax.expr
                    | uu____74972 ->
                        mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def
                          body)
             | uu____74973 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body))
        | uu____74982 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body)
  
let (resugar_pat :
  FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option ->
    FStar_Extraction_ML_Syntax.mlpattern ->
      FStar_Extraction_ML_Syntax.mlpattern)
  =
  fun q  ->
    fun p  ->
      match p with
      | FStar_Extraction_ML_Syntax.MLP_CTor (d,pats) ->
          let uu____75010 = FStar_Extraction_ML_Util.is_xtuple d  in
          (match uu____75010 with
           | FStar_Pervasives_Native.Some n1 ->
               FStar_Extraction_ML_Syntax.MLP_Tuple pats
           | uu____75017 ->
               (match q with
                | FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Record_ctor (ty,fns)) ->
                    let path =
                      FStar_List.map FStar_Ident.text_of_id ty.FStar_Ident.ns
                       in
                    let fs = record_fields fns pats  in
                    FStar_Extraction_ML_Syntax.MLP_Record (path, fs)
                | uu____75050 -> p))
      | uu____75053 -> p
  
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
                       (fun uu____75155  ->
                          let uu____75156 =
                            FStar_Extraction_ML_Code.string_of_mlty
                              g.FStar_Extraction_ML_UEnv.currentModule t'
                             in
                          let uu____75158 =
                            FStar_Extraction_ML_Code.string_of_mlty
                              g.FStar_Extraction_ML_UEnv.currentModule t
                             in
                          FStar_Util.print2
                            "Expected pattern type %s; got pattern type %s\n"
                            uu____75156 uu____75158)
                   else ();
                   ok)
               in
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int
                (c,swopt)) when
                let uu____75194 = FStar_Options.codegen ()  in
                uu____75194 <>
                  (FStar_Pervasives_Native.Some FStar_Options.Kremlin)
                ->
                let uu____75199 =
                  match swopt with
                  | FStar_Pervasives_Native.None  ->
                      let uu____75212 =
                        let uu____75213 =
                          let uu____75214 =
                            FStar_Extraction_ML_Util.mlconst_of_const
                              p.FStar_Syntax_Syntax.p
                              (FStar_Const.Const_int
                                 (c, FStar_Pervasives_Native.None))
                             in
                          FStar_Extraction_ML_Syntax.MLE_Const uu____75214
                           in
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.ml_int_ty)
                          uu____75213
                         in
                      (uu____75212, FStar_Extraction_ML_Syntax.ml_int_ty)
                  | FStar_Pervasives_Native.Some sw ->
                      let source_term =
                        FStar_ToSyntax_ToSyntax.desugar_machine_integer
                          (g.FStar_Extraction_ML_UEnv.env_tcenv).FStar_TypeChecker_Env.dsenv
                          c sw FStar_Range.dummyRange
                         in
                      let uu____75236 = term_as_mlexpr g source_term  in
                      (match uu____75236 with
                       | (mlterm,uu____75248,mlty) -> (mlterm, mlty))
                   in
                (match uu____75199 with
                 | (mlc,ml_ty) ->
                     let x = FStar_Extraction_ML_Syntax.gensym ()  in
                     let when_clause =
                       let uu____75270 =
                         let uu____75271 =
                           let uu____75278 =
                             let uu____75281 =
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty ml_ty)
                                 (FStar_Extraction_ML_Syntax.MLE_Var x)
                                in
                             [uu____75281; mlc]  in
                           (FStar_Extraction_ML_Util.prims_op_equality,
                             uu____75278)
                            in
                         FStar_Extraction_ML_Syntax.MLE_App uu____75271  in
                       FStar_All.pipe_left
                         (FStar_Extraction_ML_Syntax.with_ty
                            FStar_Extraction_ML_Syntax.ml_bool_ty)
                         uu____75270
                        in
                     let uu____75284 = ok ml_ty  in
                     (g,
                       (FStar_Pervasives_Native.Some
                          ((FStar_Extraction_ML_Syntax.MLP_Var x),
                            [when_clause])), uu____75284))
            | FStar_Syntax_Syntax.Pat_constant s ->
                let t =
                  FStar_TypeChecker_TcTerm.tc_constant
                    g.FStar_Extraction_ML_UEnv.env_tcenv
                    FStar_Range.dummyRange s
                   in
                let mlty = term_as_mlty g t  in
                let uu____75306 =
                  let uu____75315 =
                    let uu____75322 =
                      let uu____75323 =
                        FStar_Extraction_ML_Util.mlconst_of_const
                          p.FStar_Syntax_Syntax.p s
                         in
                      FStar_Extraction_ML_Syntax.MLP_Const uu____75323  in
                    (uu____75322, [])  in
                  FStar_Pervasives_Native.Some uu____75315  in
                let uu____75332 = ok mlty  in (g, uu____75306, uu____75332)
            | FStar_Syntax_Syntax.Pat_var x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort  in
                let uu____75345 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp
                   in
                (match uu____75345 with
                 | (g1,x1,uu____75373) ->
                     let uu____75376 = ok mlty  in
                     (g1,
                       (if imp
                        then FStar_Pervasives_Native.None
                        else
                          FStar_Pervasives_Native.Some
                            ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                       uu____75376))
            | FStar_Syntax_Syntax.Pat_wild x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort  in
                let uu____75414 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp
                   in
                (match uu____75414 with
                 | (g1,x1,uu____75442) ->
                     let uu____75445 = ok mlty  in
                     (g1,
                       (if imp
                        then FStar_Pervasives_Native.None
                        else
                          FStar_Pervasives_Native.Some
                            ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                       uu____75445))
            | FStar_Syntax_Syntax.Pat_dot_term uu____75481 ->
                (g, FStar_Pervasives_Native.None, true)
            | FStar_Syntax_Syntax.Pat_cons (f,pats) ->
                let uu____75524 =
                  let uu____75533 = FStar_Extraction_ML_UEnv.lookup_fv g f
                     in
                  match uu____75533 with
                  | { FStar_Extraction_ML_UEnv.exp_b_name = uu____75542;
                      FStar_Extraction_ML_UEnv.exp_b_expr =
                        {
                          FStar_Extraction_ML_Syntax.expr =
                            FStar_Extraction_ML_Syntax.MLE_Name n1;
                          FStar_Extraction_ML_Syntax.mlty = uu____75544;
                          FStar_Extraction_ML_Syntax.loc = uu____75545;_};
                      FStar_Extraction_ML_UEnv.exp_b_tscheme = ttys;
                      FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____75547;_}
                      -> (n1, ttys)
                  | uu____75554 -> failwith "Expected a constructor"  in
                (match uu____75524 with
                 | (d,tys) ->
                     let nTyVars =
                       FStar_List.length (FStar_Pervasives_Native.fst tys)
                        in
                     let uu____75591 = FStar_Util.first_N nTyVars pats  in
                     (match uu____75591 with
                      | (tysVarPats,restPats) ->
                          let f_ty_opt =
                            try
                              (fun uu___1429_75699  ->
                                 match () with
                                 | () ->
                                     let mlty_args =
                                       FStar_All.pipe_right tysVarPats
                                         (FStar_List.map
                                            (fun uu____75730  ->
                                               match uu____75730 with
                                               | (p1,uu____75737) ->
                                                   (match p1.FStar_Syntax_Syntax.v
                                                    with
                                                    | FStar_Syntax_Syntax.Pat_dot_term
                                                        (uu____75740,t) ->
                                                        term_as_mlty g t
                                                    | uu____75746 ->
                                                        (FStar_Extraction_ML_UEnv.debug
                                                           g
                                                           (fun uu____75750 
                                                              ->
                                                              let uu____75751
                                                                =
                                                                FStar_Syntax_Print.pat_to_string
                                                                  p1
                                                                 in
                                                              FStar_Util.print1
                                                                "Pattern %s is not extractable"
                                                                uu____75751);
                                                         FStar_Exn.raise
                                                           Un_extractable))))
                                        in
                                     let f_ty =
                                       FStar_Extraction_ML_Util.subst tys
                                         mlty_args
                                        in
                                     let uu____75755 =
                                       FStar_Extraction_ML_Util.uncurry_mlty_fun
                                         f_ty
                                        in
                                     FStar_Pervasives_Native.Some uu____75755)
                                ()
                            with
                            | Un_extractable  -> FStar_Pervasives_Native.None
                             in
                          let uu____75784 =
                            FStar_Util.fold_map
                              (fun g1  ->
                                 fun uu____75821  ->
                                   match uu____75821 with
                                   | (p1,imp1) ->
                                       let uu____75843 =
                                         extract_one_pat true g1 p1
                                           FStar_Pervasives_Native.None
                                           term_as_mlexpr
                                          in
                                       (match uu____75843 with
                                        | (g2,p2,uu____75874) -> (g2, p2))) g
                              tysVarPats
                             in
                          (match uu____75784 with
                           | (g1,tyMLPats) ->
                               let uu____75938 =
                                 FStar_Util.fold_map
                                   (fun uu____76003  ->
                                      fun uu____76004  ->
                                        match (uu____76003, uu____76004) with
                                        | ((g2,f_ty_opt1),(p1,imp1)) ->
                                            let uu____76102 =
                                              match f_ty_opt1 with
                                              | FStar_Pervasives_Native.Some
                                                  (hd1::rest,res) ->
                                                  ((FStar_Pervasives_Native.Some
                                                      (rest, res)),
                                                    (FStar_Pervasives_Native.Some
                                                       hd1))
                                              | uu____76162 ->
                                                  (FStar_Pervasives_Native.None,
                                                    FStar_Pervasives_Native.None)
                                               in
                                            (match uu____76102 with
                                             | (f_ty_opt2,expected_ty) ->
                                                 let uu____76233 =
                                                   extract_one_pat false g2
                                                     p1 expected_ty
                                                     term_as_mlexpr
                                                    in
                                                 (match uu____76233 with
                                                  | (g3,p2,uu____76276) ->
                                                      ((g3, f_ty_opt2), p2))))
                                   (g1, f_ty_opt) restPats
                                  in
                               (match uu____75938 with
                                | ((g2,f_ty_opt1),restMLPats) ->
                                    let uu____76397 =
                                      let uu____76408 =
                                        FStar_All.pipe_right
                                          (FStar_List.append tyMLPats
                                             restMLPats)
                                          (FStar_List.collect
                                             (fun uu___618_76459  ->
                                                match uu___618_76459 with
                                                | FStar_Pervasives_Native.Some
                                                    x -> [x]
                                                | uu____76501 -> []))
                                         in
                                      FStar_All.pipe_right uu____76408
                                        FStar_List.split
                                       in
                                    (match uu____76397 with
                                     | (mlPats,when_clauses) ->
                                         let pat_ty_compat =
                                           match f_ty_opt1 with
                                           | FStar_Pervasives_Native.Some
                                               ([],t) -> ok t
                                           | uu____76577 -> false  in
                                         let uu____76587 =
                                           let uu____76596 =
                                             let uu____76603 =
                                               resugar_pat
                                                 f.FStar_Syntax_Syntax.fv_qual
                                                 (FStar_Extraction_ML_Syntax.MLP_CTor
                                                    (d, mlPats))
                                                in
                                             let uu____76606 =
                                               FStar_All.pipe_right
                                                 when_clauses
                                                 FStar_List.flatten
                                                in
                                             (uu____76603, uu____76606)  in
                                           FStar_Pervasives_Native.Some
                                             uu____76596
                                            in
                                         (g2, uu____76587, pat_ty_compat))))))
  
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
            let uu____76738 =
              extract_one_pat false g1 p1 expected_t1 term_as_mlexpr  in
            match uu____76738 with
            | (g2,FStar_Pervasives_Native.Some (x,v1),b) -> (g2, (x, v1), b)
            | uu____76801 ->
                failwith "Impossible: Unable to translate pattern"
             in
          let mk_when_clause whens =
            match whens with
            | [] -> FStar_Pervasives_Native.None
            | hd1::tl1 ->
                let uu____76849 =
                  FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd1
                    tl1
                   in
                FStar_Pervasives_Native.Some uu____76849
             in
          let uu____76850 =
            extract_one_pat1 g p (FStar_Pervasives_Native.Some expected_t)
             in
          match uu____76850 with
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
            | FStar_Extraction_ML_Syntax.MLTY_Fun (t0,uu____77010,t1) ->
                let x = FStar_Extraction_ML_Syntax.gensym ()  in
                let uu____77014 =
                  let uu____77026 =
                    let uu____77036 =
                      FStar_All.pipe_left
                        (FStar_Extraction_ML_Syntax.with_ty t0)
                        (FStar_Extraction_ML_Syntax.MLE_Var x)
                       in
                    ((x, t0), uu____77036)  in
                  uu____77026 :: more_args  in
                eta_args uu____77014 t1
            | FStar_Extraction_ML_Syntax.MLTY_Named (uu____77052,uu____77053)
                -> ((FStar_List.rev more_args), t)
            | uu____77078 ->
                let uu____77079 =
                  let uu____77081 =
                    FStar_Extraction_ML_Code.string_of_mlexpr
                      g.FStar_Extraction_ML_UEnv.currentModule mlAppExpr
                     in
                  let uu____77083 =
                    FStar_Extraction_ML_Code.string_of_mlty
                      g.FStar_Extraction_ML_UEnv.currentModule t
                     in
                  FStar_Util.format2
                    "Impossible: Head type is not an arrow: (%s : %s)"
                    uu____77081 uu____77083
                   in
                failwith uu____77079
             in
          let as_record qual1 e =
            match ((e.FStar_Extraction_ML_Syntax.expr), qual1) with
            | (FStar_Extraction_ML_Syntax.MLE_CTor
               (uu____77118,args),FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Record_ctor (tyname,fields))) ->
                let path =
                  FStar_List.map FStar_Ident.text_of_id tyname.FStar_Ident.ns
                   in
                let fields1 = record_fields fields args  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     e.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_Record (path, fields1))
            | uu____77155 -> e  in
          let resugar_and_maybe_eta qual1 e =
            let uu____77177 = eta_args [] residualType  in
            match uu____77177 with
            | (eargs,tres) ->
                (match eargs with
                 | [] ->
                     let uu____77235 = as_record qual1 e  in
                     FStar_Extraction_ML_Util.resugar_exp uu____77235
                 | uu____77236 ->
                     let uu____77248 = FStar_List.unzip eargs  in
                     (match uu____77248 with
                      | (binders,eargs1) ->
                          (match e.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_CTor (head1,args)
                               ->
                               let body =
                                 let uu____77294 =
                                   let uu____77295 =
                                     FStar_All.pipe_left
                                       (FStar_Extraction_ML_Syntax.with_ty
                                          tres)
                                       (FStar_Extraction_ML_Syntax.MLE_CTor
                                          (head1,
                                            (FStar_List.append args eargs1)))
                                      in
                                   FStar_All.pipe_left (as_record qual1)
                                     uu____77295
                                    in
                                 FStar_All.pipe_left
                                   FStar_Extraction_ML_Util.resugar_exp
                                   uu____77294
                                  in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    e.FStar_Extraction_ML_Syntax.mlty)
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    (binders, body))
                           | uu____77305 ->
                               failwith "Impossible: Not a constructor")))
             in
          match ((mlAppExpr.FStar_Extraction_ML_Syntax.expr), qual) with
          | (uu____77309,FStar_Pervasives_Native.None ) -> mlAppExpr
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____77313;
                FStar_Extraction_ML_Syntax.loc = uu____77314;_},mle::args),FStar_Pervasives_Native.Some
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
                | uu____77337 ->
                    let uu____77340 =
                      let uu____77347 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj
                         in
                      (uu____77347, args)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____77340
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
                     FStar_Extraction_ML_Syntax.mlty = uu____77351;
                     FStar_Extraction_ML_Syntax.loc = uu____77352;_},uu____77353);
                FStar_Extraction_ML_Syntax.mlty = uu____77354;
                FStar_Extraction_ML_Syntax.loc = uu____77355;_},mle::args),FStar_Pervasives_Native.Some
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
                | uu____77382 ->
                    let uu____77385 =
                      let uu____77392 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj
                         in
                      (uu____77392, args)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____77385
                 in
              FStar_Extraction_ML_Syntax.with_ty
                mlAppExpr.FStar_Extraction_ML_Syntax.mlty e
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____77396;
                FStar_Extraction_ML_Syntax.loc = uu____77397;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____77405 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____77405
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____77409;
                FStar_Extraction_ML_Syntax.loc = uu____77410;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____77412)) ->
              let uu____77425 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____77425
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____77429;
                     FStar_Extraction_ML_Syntax.loc = uu____77430;_},uu____77431);
                FStar_Extraction_ML_Syntax.mlty = uu____77432;
                FStar_Extraction_ML_Syntax.loc = uu____77433;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____77445 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____77445
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____77449;
                     FStar_Extraction_ML_Syntax.loc = uu____77450;_},uu____77451);
                FStar_Extraction_ML_Syntax.mlty = uu____77452;
                FStar_Extraction_ML_Syntax.loc = uu____77453;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____77455)) ->
              let uu____77472 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____77472
          | (FStar_Extraction_ML_Syntax.MLE_Name
             mlp,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor
             )) ->
              let uu____77478 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____77478
          | (FStar_Extraction_ML_Syntax.MLE_Name
             mlp,FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____77482)) ->
              let uu____77491 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____77491
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____77495;
                FStar_Extraction_ML_Syntax.loc = uu____77496;_},uu____77497),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____77504 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____77504
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____77508;
                FStar_Extraction_ML_Syntax.loc = uu____77509;_},uu____77510),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____77511)) ->
              let uu____77524 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____77524
          | uu____77527 -> mlAppExpr
  
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
        | uu____77558 -> (ml_e, tag)
  
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
      let maybe_generalize uu____77619 =
        match uu____77619 with
        | { FStar_Syntax_Syntax.lbname = lbname_;
            FStar_Syntax_Syntax.lbunivs = uu____77640;
            FStar_Syntax_Syntax.lbtyp = lbtyp;
            FStar_Syntax_Syntax.lbeff = lbeff;
            FStar_Syntax_Syntax.lbdef = lbdef;
            FStar_Syntax_Syntax.lbattrs = uu____77644;
            FStar_Syntax_Syntax.lbpos = uu____77645;_} ->
            let f_e = effect_as_etag g lbeff  in
            let lbtyp1 = FStar_Syntax_Subst.compress lbtyp  in
            let no_gen uu____77726 =
              let expected_t = term_as_mlty g lbtyp1  in
              (lbname_, f_e, (lbtyp1, ([], ([], expected_t))), false, lbdef)
               in
            let uu____77803 =
              FStar_TypeChecker_Util.must_erase_for_extraction
                g.FStar_Extraction_ML_UEnv.env_tcenv lbtyp1
               in
            if uu____77803
            then
              (lbname_, f_e,
                (lbtyp1, ([], ([], FStar_Extraction_ML_Syntax.MLTY_Erased))),
                false, lbdef)
            else
              (match lbtyp1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                   let uu____77889 = FStar_List.hd bs  in
                   FStar_All.pipe_right uu____77889 (is_type_binder g) ->
                   let uu____77911 = FStar_Syntax_Subst.open_comp bs c  in
                   (match uu____77911 with
                    | (bs1,c1) ->
                        let uu____77937 =
                          let uu____77950 =
                            FStar_Util.prefix_until
                              (fun x  ->
                                 let uu____77996 = is_type_binder g x  in
                                 Prims.op_Negation uu____77996) bs1
                             in
                          match uu____77950 with
                          | FStar_Pervasives_Native.None  ->
                              (bs1, (FStar_Syntax_Util.comp_result c1))
                          | FStar_Pervasives_Native.Some (bs2,b,rest) ->
                              let uu____78123 =
                                FStar_Syntax_Util.arrow (b :: rest) c1  in
                              (bs2, uu____78123)
                           in
                        (match uu____77937 with
                         | (tbinders,tbody) ->
                             let n_tbinders = FStar_List.length tbinders  in
                             let lbdef1 =
                               let uu____78185 = normalize_abs lbdef  in
                               FStar_All.pipe_right uu____78185
                                 FStar_Syntax_Util.unmeta
                                in
                             (match lbdef1.FStar_Syntax_Syntax.n with
                              | FStar_Syntax_Syntax.Tm_abs (bs2,body,copt) ->
                                  let uu____78234 =
                                    FStar_Syntax_Subst.open_term bs2 body  in
                                  (match uu____78234 with
                                   | (bs3,body1) ->
                                       if
                                         n_tbinders <=
                                           (FStar_List.length bs3)
                                       then
                                         let uu____78292 =
                                           FStar_Util.first_N n_tbinders bs3
                                            in
                                         (match uu____78292 with
                                          | (targs,rest_args) ->
                                              let expected_source_ty =
                                                let s =
                                                  FStar_List.map2
                                                    (fun uu____78399  ->
                                                       fun uu____78400  ->
                                                         match (uu____78399,
                                                                 uu____78400)
                                                         with
                                                         | ((x,uu____78426),
                                                            (y,uu____78428))
                                                             ->
                                                             let uu____78449
                                                               =
                                                               let uu____78456
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   y
                                                                  in
                                                               (x,
                                                                 uu____78456)
                                                                in
                                                             FStar_Syntax_Syntax.NT
                                                               uu____78449)
                                                    tbinders targs
                                                   in
                                                FStar_Syntax_Subst.subst s
                                                  tbody
                                                 in
                                              let env =
                                                FStar_List.fold_left
                                                  (fun env  ->
                                                     fun uu____78473  ->
                                                       match uu____78473 with
                                                       | (a,uu____78481) ->
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
                                                let uu____78492 =
                                                  FStar_All.pipe_right targs
                                                    (FStar_List.map
                                                       (fun uu____78511  ->
                                                          match uu____78511
                                                          with
                                                          | (x,uu____78520)
                                                              ->
                                                              FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                                x))
                                                   in
                                                (uu____78492, expected_t)  in
                                              let add_unit =
                                                match rest_args with
                                                | [] ->
                                                    (let uu____78536 =
                                                       is_fstar_value body1
                                                        in
                                                     Prims.op_Negation
                                                       uu____78536)
                                                      ||
                                                      (let uu____78539 =
                                                         FStar_Syntax_Util.is_pure_comp
                                                           c1
                                                          in
                                                       Prims.op_Negation
                                                         uu____78539)
                                                | uu____78541 -> false  in
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
                              | FStar_Syntax_Syntax.Tm_uinst uu____78603 ->
                                  let env =
                                    FStar_List.fold_left
                                      (fun env  ->
                                         fun uu____78622  ->
                                           match uu____78622 with
                                           | (a,uu____78630) ->
                                               FStar_Extraction_ML_UEnv.extend_ty
                                                 env a
                                                 FStar_Pervasives_Native.None)
                                      g tbinders
                                     in
                                  let expected_t = term_as_mlty env tbody  in
                                  let polytype =
                                    let uu____78641 =
                                      FStar_All.pipe_right tbinders
                                        (FStar_List.map
                                           (fun uu____78660  ->
                                              match uu____78660 with
                                              | (x,uu____78669) ->
                                                  FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                    x))
                                       in
                                    (uu____78641, expected_t)  in
                                  let args =
                                    FStar_All.pipe_right tbinders
                                      (FStar_List.map
                                         (fun uu____78713  ->
                                            match uu____78713 with
                                            | (bv,uu____78721) ->
                                                let uu____78726 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    bv
                                                   in
                                                FStar_All.pipe_right
                                                  uu____78726
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
                              | FStar_Syntax_Syntax.Tm_fvar uu____78756 ->
                                  let env =
                                    FStar_List.fold_left
                                      (fun env  ->
                                         fun uu____78769  ->
                                           match uu____78769 with
                                           | (a,uu____78777) ->
                                               FStar_Extraction_ML_UEnv.extend_ty
                                                 env a
                                                 FStar_Pervasives_Native.None)
                                      g tbinders
                                     in
                                  let expected_t = term_as_mlty env tbody  in
                                  let polytype =
                                    let uu____78788 =
                                      FStar_All.pipe_right tbinders
                                        (FStar_List.map
                                           (fun uu____78807  ->
                                              match uu____78807 with
                                              | (x,uu____78816) ->
                                                  FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                    x))
                                       in
                                    (uu____78788, expected_t)  in
                                  let args =
                                    FStar_All.pipe_right tbinders
                                      (FStar_List.map
                                         (fun uu____78860  ->
                                            match uu____78860 with
                                            | (bv,uu____78868) ->
                                                let uu____78873 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    bv
                                                   in
                                                FStar_All.pipe_right
                                                  uu____78873
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
                              | FStar_Syntax_Syntax.Tm_name uu____78903 ->
                                  let env =
                                    FStar_List.fold_left
                                      (fun env  ->
                                         fun uu____78916  ->
                                           match uu____78916 with
                                           | (a,uu____78924) ->
                                               FStar_Extraction_ML_UEnv.extend_ty
                                                 env a
                                                 FStar_Pervasives_Native.None)
                                      g tbinders
                                     in
                                  let expected_t = term_as_mlty env tbody  in
                                  let polytype =
                                    let uu____78935 =
                                      FStar_All.pipe_right tbinders
                                        (FStar_List.map
                                           (fun uu____78954  ->
                                              match uu____78954 with
                                              | (x,uu____78963) ->
                                                  FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                    x))
                                       in
                                    (uu____78935, expected_t)  in
                                  let args =
                                    FStar_All.pipe_right tbinders
                                      (FStar_List.map
                                         (fun uu____79007  ->
                                            match uu____79007 with
                                            | (bv,uu____79015) ->
                                                let uu____79020 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    bv
                                                   in
                                                FStar_All.pipe_right
                                                  uu____79020
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
                              | uu____79050 -> err_value_restriction lbdef1)))
               | uu____79070 -> no_gen ())
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
           fun uu____79221  ->
             match uu____79221 with
             | (lbname,e_tag,(typ,(binders,mltyscheme)),add_unit,_body) ->
                 let uu____79282 =
                   FStar_Extraction_ML_UEnv.extend_lb env lbname typ
                     mltyscheme add_unit is_rec
                    in
                 (match uu____79282 with
                  | (env1,uu____79299,exp_binding) ->
                      let uu____79303 =
                        let uu____79308 = FStar_Util.right lbname  in
                        (uu____79308, exp_binding)  in
                      (env1, uu____79303))) g lbs1
  
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
            (fun uu____79374  ->
               let uu____79375 = FStar_Syntax_Print.term_to_string e  in
               let uu____79377 =
                 FStar_Extraction_ML_Code.string_of_mlty
                   g.FStar_Extraction_ML_UEnv.currentModule ty
                  in
               FStar_Util.print2 "Checking %s at type %s\n" uu____79375
                 uu____79377);
          (match (f, ty) with
           | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____79384) ->
               (FStar_Extraction_ML_Syntax.ml_unit,
                 FStar_Extraction_ML_Syntax.MLTY_Erased)
           | (FStar_Extraction_ML_Syntax.E_PURE
              ,FStar_Extraction_ML_Syntax.MLTY_Erased ) ->
               (FStar_Extraction_ML_Syntax.ml_unit,
                 FStar_Extraction_ML_Syntax.MLTY_Erased)
           | uu____79385 ->
               let uu____79390 = term_as_mlexpr g e  in
               (match uu____79390 with
                | (ml_e,tag,t) ->
                    let uu____79404 = maybe_promote_effect ml_e tag t  in
                    (match uu____79404 with
                     | (ml_e1,tag1) ->
                         let uu____79415 =
                           FStar_Extraction_ML_Util.eff_leq tag1 f  in
                         if uu____79415
                         then
                           let uu____79422 =
                             maybe_coerce e.FStar_Syntax_Syntax.pos g ml_e1 t
                               ty
                              in
                           (uu____79422, ty)
                         else
                           (match (tag1, f, ty) with
                            | (FStar_Extraction_ML_Syntax.E_GHOST
                               ,FStar_Extraction_ML_Syntax.E_PURE
                               ,FStar_Extraction_ML_Syntax.MLTY_Erased ) ->
                                let uu____79429 =
                                  maybe_coerce e.FStar_Syntax_Syntax.pos g
                                    ml_e1 t ty
                                   in
                                (uu____79429, ty)
                            | uu____79430 ->
                                (err_unexpected_eff g e ty f tag1;
                                 (let uu____79438 =
                                    maybe_coerce e.FStar_Syntax_Syntax.pos g
                                      ml_e1 t ty
                                     in
                                  (uu____79438, ty)))))))

and (term_as_mlexpr :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag *
        FStar_Extraction_ML_Syntax.mlty))
  =
  fun g  ->
    fun e  ->
      let uu____79441 = term_as_mlexpr' g e  in
      match uu____79441 with
      | (e1,f,t) ->
          let uu____79457 = maybe_promote_effect e1 f t  in
          (match uu____79457 with | (e2,f1) -> (e2, f1, t))

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
           let uu____79482 =
             let uu____79484 =
               FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos  in
             let uu____79486 = FStar_Syntax_Print.tag_of_term top  in
             let uu____79488 = FStar_Syntax_Print.term_to_string top  in
             FStar_Util.format3 "%s: term_as_mlexpr' (%s) :  %s \n"
               uu____79484 uu____79486 uu____79488
              in
           FStar_Util.print_string uu____79482);
      (let t = FStar_Syntax_Subst.compress top  in
       match t.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____79498 =
             let uu____79500 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____79500
              in
           failwith uu____79498
       | FStar_Syntax_Syntax.Tm_delayed uu____79509 ->
           let uu____79532 =
             let uu____79534 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____79534
              in
           failwith uu____79532
       | FStar_Syntax_Syntax.Tm_uvar uu____79543 ->
           let uu____79556 =
             let uu____79558 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____79558
              in
           failwith uu____79556
       | FStar_Syntax_Syntax.Tm_bvar uu____79567 ->
           let uu____79568 =
             let uu____79570 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____79570
              in
           failwith uu____79568
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____79580 = FStar_Syntax_Util.unfold_lazy i  in
           term_as_mlexpr g uu____79580
       | FStar_Syntax_Syntax.Tm_type uu____79581 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_refine uu____79582 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_arrow uu____79589 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_quoted
           (qt,{
                 FStar_Syntax_Syntax.qkind =
                   FStar_Syntax_Syntax.Quote_dynamic ;
                 FStar_Syntax_Syntax.antiquotes = uu____79605;_})
           ->
           let uu____79618 =
             let uu____79619 =
               FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.failwith_lid
                 FStar_Syntax_Syntax.delta_constant
                 FStar_Pervasives_Native.None
                in
             FStar_Extraction_ML_UEnv.lookup_fv g uu____79619  in
           (match uu____79618 with
            | { FStar_Extraction_ML_UEnv.exp_b_name = uu____79626;
                FStar_Extraction_ML_UEnv.exp_b_expr = fw;
                FStar_Extraction_ML_UEnv.exp_b_tscheme = uu____79628;
                FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____79629;_} ->
                let uu____79632 =
                  let uu____79633 =
                    let uu____79634 =
                      let uu____79641 =
                        let uu____79644 =
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty
                               FStar_Extraction_ML_Syntax.ml_string_ty)
                            (FStar_Extraction_ML_Syntax.MLE_Const
                               (FStar_Extraction_ML_Syntax.MLC_String
                                  "Cannot evaluate open quotation at runtime"))
                           in
                        [uu____79644]  in
                      (fw, uu____79641)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____79634  in
                  FStar_All.pipe_left
                    (FStar_Extraction_ML_Syntax.with_ty
                       FStar_Extraction_ML_Syntax.ml_int_ty) uu____79633
                   in
                (uu____79632, FStar_Extraction_ML_Syntax.E_PURE,
                  FStar_Extraction_ML_Syntax.ml_int_ty))
       | FStar_Syntax_Syntax.Tm_quoted
           (qt,{
                 FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static ;
                 FStar_Syntax_Syntax.antiquotes = aqs;_})
           ->
           let uu____79662 = FStar_Reflection_Basic.inspect_ln qt  in
           (match uu____79662 with
            | FStar_Reflection_Data.Tv_Var bv ->
                let uu____79670 = FStar_Syntax_Syntax.lookup_aq bv aqs  in
                (match uu____79670 with
                 | FStar_Pervasives_Native.Some tm -> term_as_mlexpr g tm
                 | FStar_Pervasives_Native.None  ->
                     let tv =
                       let uu____79681 =
                         let uu____79688 =
                           FStar_Reflection_Embeddings.e_term_view_aq aqs  in
                         FStar_Syntax_Embeddings.embed uu____79688
                           (FStar_Reflection_Data.Tv_Var bv)
                          in
                       uu____79681 t.FStar_Syntax_Syntax.pos
                         FStar_Pervasives_Native.None
                         FStar_Syntax_Embeddings.id_norm_cb
                        in
                     let t1 =
                       let uu____79719 =
                         let uu____79730 = FStar_Syntax_Syntax.as_arg tv  in
                         [uu____79730]  in
                       FStar_Syntax_Util.mk_app
                         (FStar_Reflection_Data.refl_constant_term
                            FStar_Reflection_Data.fstar_refl_pack_ln)
                         uu____79719
                        in
                     term_as_mlexpr g t1)
            | tv ->
                let tv1 =
                  let uu____79757 =
                    let uu____79764 =
                      FStar_Reflection_Embeddings.e_term_view_aq aqs  in
                    FStar_Syntax_Embeddings.embed uu____79764 tv  in
                  uu____79757 t.FStar_Syntax_Syntax.pos
                    FStar_Pervasives_Native.None
                    FStar_Syntax_Embeddings.id_norm_cb
                   in
                let t1 =
                  let uu____79795 =
                    let uu____79806 = FStar_Syntax_Syntax.as_arg tv1  in
                    [uu____79806]  in
                  FStar_Syntax_Util.mk_app
                    (FStar_Reflection_Data.refl_constant_term
                       FStar_Reflection_Data.fstar_refl_pack_ln) uu____79795
                   in
                term_as_mlexpr g t1)
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_monadic (m,uu____79833)) ->
           let t2 = FStar_Syntax_Subst.compress t1  in
           (match t2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) when
                FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname ->
                let uu____79866 =
                  let uu____79873 =
                    FStar_TypeChecker_Env.effect_decl_opt
                      g.FStar_Extraction_ML_UEnv.env_tcenv m
                     in
                  FStar_Util.must uu____79873  in
                (match uu____79866 with
                 | (ed,qualifiers) ->
                     let uu____79900 =
                       let uu____79902 =
                         FStar_TypeChecker_Env.is_reifiable_effect
                           g.FStar_Extraction_ML_UEnv.env_tcenv
                           ed.FStar_Syntax_Syntax.mname
                          in
                       Prims.op_Negation uu____79902  in
                     if uu____79900
                     then term_as_mlexpr g t2
                     else
                       failwith
                         "This should not happen (should have been handled at Tm_abs level)")
            | uu____79920 -> term_as_mlexpr g t2)
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____79922) -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____79928) -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____79934 =
             FStar_TypeChecker_TcTerm.type_of_tot_term
               g.FStar_Extraction_ML_UEnv.env_tcenv t
              in
           (match uu____79934 with
            | (uu____79947,ty,uu____79949) ->
                let ml_ty = term_as_mlty g ty  in
                let uu____79951 =
                  let uu____79952 =
                    FStar_Extraction_ML_Util.mlexpr_of_const
                      t.FStar_Syntax_Syntax.pos c
                     in
                  FStar_Extraction_ML_Syntax.with_ty ml_ty uu____79952  in
                (uu____79951, FStar_Extraction_ML_Syntax.E_PURE, ml_ty))
       | FStar_Syntax_Syntax.Tm_name uu____79953 ->
           let uu____79954 = is_type g t  in
           if uu____79954
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____79965 = FStar_Extraction_ML_UEnv.lookup_term g t  in
              match uu____79965 with
              | (FStar_Util.Inl uu____79978,uu____79979) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | (FStar_Util.Inr
                 { FStar_Extraction_ML_UEnv.exp_b_name = uu____79984;
                   FStar_Extraction_ML_UEnv.exp_b_expr = x;
                   FStar_Extraction_ML_UEnv.exp_b_tscheme = mltys;
                   FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____79987;_},qual)
                  ->
                  (match mltys with
                   | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                       ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | ([],t1) ->
                       let uu____80005 =
                         maybe_eta_data_and_project_record g qual t1 x  in
                       (uu____80005, FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | uu____80006 -> err_uninst g t mltys t))
       | FStar_Syntax_Syntax.Tm_fvar fv ->
           let uu____80014 = is_type g t  in
           if uu____80014
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____80025 = FStar_Extraction_ML_UEnv.try_lookup_fv g fv
                 in
              match uu____80025 with
              | FStar_Pervasives_Native.None  ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.MLTY_Erased)
              | FStar_Pervasives_Native.Some
                  { FStar_Extraction_ML_UEnv.exp_b_name = uu____80034;
                    FStar_Extraction_ML_UEnv.exp_b_expr = x;
                    FStar_Extraction_ML_UEnv.exp_b_tscheme = mltys;
                    FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____80037;_}
                  ->
                  (FStar_Extraction_ML_UEnv.debug g
                     (fun uu____80045  ->
                        let uu____80046 = FStar_Syntax_Print.fv_to_string fv
                           in
                        let uu____80048 =
                          FStar_Extraction_ML_Code.string_of_mlexpr
                            g.FStar_Extraction_ML_UEnv.currentModule x
                           in
                        let uu____80050 =
                          FStar_Extraction_ML_Code.string_of_mlty
                            g.FStar_Extraction_ML_UEnv.currentModule
                            (FStar_Pervasives_Native.snd mltys)
                           in
                        FStar_Util.print3 "looked up %s: got %s at %s \n"
                          uu____80046 uu____80048 uu____80050);
                   (match mltys with
                    | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                        ->
                        (FStar_Extraction_ML_Syntax.ml_unit,
                          FStar_Extraction_ML_Syntax.E_PURE, t1)
                    | ([],t1) ->
                        let uu____80063 =
                          maybe_eta_data_and_project_record g
                            fv.FStar_Syntax_Syntax.fv_qual t1 x
                           in
                        (uu____80063, FStar_Extraction_ML_Syntax.E_PURE, t1)
                    | uu____80064 -> err_uninst g t mltys t)))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,rcopt) ->
           let uu____80098 = FStar_Syntax_Subst.open_term bs body  in
           (match uu____80098 with
            | (bs1,body1) ->
                let uu____80111 = binders_as_ml_binders g bs1  in
                (match uu____80111 with
                 | (ml_bs,env) ->
                     let body2 =
                       match rcopt with
                       | FStar_Pervasives_Native.Some rc ->
                           let uu____80147 =
                             FStar_TypeChecker_Env.is_reifiable_rc
                               env.FStar_Extraction_ML_UEnv.env_tcenv rc
                              in
                           if uu____80147
                           then
                             FStar_TypeChecker_Util.reify_body
                               env.FStar_Extraction_ML_UEnv.env_tcenv body1
                           else body1
                       | FStar_Pervasives_Native.None  ->
                           (FStar_Extraction_ML_UEnv.debug g
                              (fun uu____80155  ->
                                 let uu____80156 =
                                   FStar_Syntax_Print.term_to_string body1
                                    in
                                 FStar_Util.print1
                                   "No computation type for: %s\n"
                                   uu____80156);
                            body1)
                        in
                     let uu____80159 = term_as_mlexpr env body2  in
                     (match uu____80159 with
                      | (ml_body,f,t1) ->
                          let uu____80175 =
                            FStar_List.fold_right
                              (fun uu____80195  ->
                                 fun uu____80196  ->
                                   match (uu____80195, uu____80196) with
                                   | ((uu____80219,targ),(f1,t2)) ->
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         (FStar_Extraction_ML_Syntax.MLTY_Fun
                                            (targ, f1, t2)))) ml_bs (f, t1)
                             in
                          (match uu____80175 with
                           | (f1,tfun) ->
                               let uu____80242 =
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty tfun)
                                   (FStar_Extraction_ML_Syntax.MLE_Fun
                                      (ml_bs, ml_body))
                                  in
                               (uu____80242, f1, tfun)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____80250;
              FStar_Syntax_Syntax.vars = uu____80251;_},(a1,uu____80253)::[])
           ->
           let ty =
             let uu____80293 =
               FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid  in
             term_as_mlty g uu____80293  in
           let uu____80294 =
             let uu____80295 =
               FStar_Extraction_ML_Util.mlexpr_of_range
                 a1.FStar_Syntax_Syntax.pos
                in
             FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty)
               uu____80295
              in
           (uu____80294, FStar_Extraction_ML_Syntax.E_PURE, ty)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____80296;
              FStar_Syntax_Syntax.vars = uu____80297;_},(t1,uu____80299)::
            (r,uu____80301)::[])
           -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____80356);
              FStar_Syntax_Syntax.pos = uu____80357;
              FStar_Syntax_Syntax.vars = uu____80358;_},uu____80359)
           -> failwith "Unreachable? Tm_app Const_reflect"
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let is_total rc =
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_Tot_lid)
               ||
               (FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
                  (FStar_List.existsb
                     (fun uu___619_80428  ->
                        match uu___619_80428 with
                        | FStar_Syntax_Syntax.TOTAL  -> true
                        | uu____80431 -> false)))
              in
           let uu____80433 =
             let uu____80438 =
               let uu____80439 = FStar_Syntax_Subst.compress head1  in
               uu____80439.FStar_Syntax_Syntax.n  in
             ((head1.FStar_Syntax_Syntax.n), uu____80438)  in
           (match uu____80433 with
            | (FStar_Syntax_Syntax.Tm_uvar uu____80448,uu____80449) ->
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
            | (uu____80463,FStar_Syntax_Syntax.Tm_abs
               (bs,uu____80465,FStar_Pervasives_Native.Some rc)) when
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
            | (uu____80490,FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_reify )) ->
                let e =
                  let uu____80492 = FStar_List.hd args  in
                  FStar_TypeChecker_Util.reify_body_with_arg
                    g.FStar_Extraction_ML_UEnv.env_tcenv head1 uu____80492
                   in
                let tm =
                  let uu____80504 =
                    let uu____80509 = FStar_TypeChecker_Util.remove_reify e
                       in
                    let uu____80510 = FStar_List.tl args  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____80509 uu____80510  in
                  uu____80504 FStar_Pervasives_Native.None
                    t.FStar_Syntax_Syntax.pos
                   in
                term_as_mlexpr g tm
            | uu____80521 ->
                let rec extract_app is_data uu____80574 uu____80575 restArgs
                  =
                  match (uu____80574, uu____80575) with
                  | ((mlhead,mlargs_f),(f,t1)) ->
                      let mk_head uu____80656 =
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
                         (fun uu____80683  ->
                            let uu____80684 =
                              let uu____80686 = mk_head ()  in
                              FStar_Extraction_ML_Code.string_of_mlexpr
                                g.FStar_Extraction_ML_UEnv.currentModule
                                uu____80686
                               in
                            let uu____80687 =
                              FStar_Extraction_ML_Code.string_of_mlty
                                g.FStar_Extraction_ML_UEnv.currentModule t1
                               in
                            let uu____80689 =
                              match restArgs with
                              | [] -> "none"
                              | (hd1,uu____80700)::uu____80701 ->
                                  FStar_Syntax_Print.term_to_string hd1
                               in
                            FStar_Util.print3
                              "extract_app ml_head=%s type of head = %s, next arg = %s\n"
                              uu____80684 uu____80687 uu____80689);
                       (match (restArgs, t1) with
                        | ([],uu____80735) ->
                            let app =
                              let uu____80751 = mk_head ()  in
                              maybe_eta_data_and_project_record g is_data t1
                                uu____80751
                               in
                            (app, f, t1)
                        | ((arg,uu____80753)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                           (formal_t,f',t2)) when
                            (is_type g arg) &&
                              (type_leq g formal_t
                                 FStar_Extraction_ML_Syntax.ml_unit_ty)
                            ->
                            let uu____80784 =
                              let uu____80789 =
                                FStar_Extraction_ML_Util.join
                                  arg.FStar_Syntax_Syntax.pos f f'
                                 in
                              (uu____80789, t2)  in
                            extract_app is_data
                              (mlhead,
                                ((FStar_Extraction_ML_Syntax.ml_unit,
                                   FStar_Extraction_ML_Syntax.E_PURE) ::
                                mlargs_f)) uu____80784 rest
                        | ((e0,uu____80801)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                           (tExpected,f',t2)) ->
                            let r = e0.FStar_Syntax_Syntax.pos  in
                            let expected_effect =
                              let uu____80834 =
                                (FStar_Options.lax ()) &&
                                  (FStar_TypeChecker_Util.short_circuit_head
                                     head1)
                                 in
                              if uu____80834
                              then FStar_Extraction_ML_Syntax.E_IMPURE
                              else FStar_Extraction_ML_Syntax.E_PURE  in
                            let uu____80839 =
                              check_term_as_mlexpr g e0 expected_effect
                                tExpected
                               in
                            (match uu____80839 with
                             | (e01,tInferred) ->
                                 let uu____80852 =
                                   let uu____80857 =
                                     FStar_Extraction_ML_Util.join_l r
                                       [f; f']
                                      in
                                   (uu____80857, t2)  in
                                 extract_app is_data
                                   (mlhead, ((e01, expected_effect) ::
                                     mlargs_f)) uu____80852 rest)
                        | uu____80868 ->
                            let uu____80881 =
                              FStar_Extraction_ML_Util.udelta_unfold g t1  in
                            (match uu____80881 with
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
                                  | uu____80953 ->
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
                let extract_app_maybe_projector is_data mlhead uu____81024
                  args1 =
                  match uu____81024 with
                  | (f,t1) ->
                      (match is_data with
                       | FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_projector uu____81054)
                           ->
                           let rec remove_implicits args2 f1 t2 =
                             match (args2, t2) with
                             | ((a0,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____81138))::args3,FStar_Extraction_ML_Syntax.MLTY_Fun
                                (uu____81140,f',t3)) ->
                                 let uu____81178 =
                                   FStar_Extraction_ML_Util.join
                                     a0.FStar_Syntax_Syntax.pos f1 f'
                                    in
                                 remove_implicits args3 uu____81178 t3
                             | uu____81179 -> (args2, f1, t2)  in
                           let uu____81204 = remove_implicits args1 f t1  in
                           (match uu____81204 with
                            | (args2,f1,t2) ->
                                extract_app is_data (mlhead, []) (f1, t2)
                                  args2)
                       | uu____81260 ->
                           extract_app is_data (mlhead, []) (f, t1) args1)
                   in
                let extract_app_with_instantiations uu____81284 =
                  let head2 = FStar_Syntax_Util.un_uinst head1  in
                  match head2.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_name uu____81292 ->
                      let uu____81293 =
                        let uu____81314 =
                          FStar_Extraction_ML_UEnv.lookup_term g head2  in
                        match uu____81314 with
                        | (FStar_Util.Inr exp_b,q) ->
                            (FStar_Extraction_ML_UEnv.debug g
                               (fun uu____81353  ->
                                  let uu____81354 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  let uu____81356 =
                                    FStar_Extraction_ML_Code.string_of_mlexpr
                                      g.FStar_Extraction_ML_UEnv.currentModule
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_expr
                                     in
                                  let uu____81358 =
                                    FStar_Extraction_ML_Code.string_of_mlty
                                      g.FStar_Extraction_ML_UEnv.currentModule
                                      (FStar_Pervasives_Native.snd
                                         exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme)
                                     in
                                  let uu____81360 =
                                    FStar_Util.string_of_bool
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok
                                     in
                                  FStar_Util.print4
                                    "@@@looked up %s: got %s at %s (inst_ok=%s)\n"
                                    uu____81354 uu____81356 uu____81358
                                    uu____81360);
                             (((exp_b.FStar_Extraction_ML_UEnv.exp_b_expr),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok)),
                               q))
                        | uu____81387 -> failwith "FIXME Ty"  in
                      (match uu____81293 with
                       | ((head_ml,(vars,t1),inst_ok),qual) ->
                           let has_typ_apps =
                             match args with
                             | (a,uu____81463)::uu____81464 -> is_type g a
                             | uu____81491 -> false  in
                           let uu____81503 =
                             match vars with
                             | uu____81532::uu____81533 when
                                 (Prims.op_Negation has_typ_apps) && inst_ok
                                 -> (head_ml, t1, args)
                             | uu____81547 ->
                                 let n1 = FStar_List.length vars  in
                                 if n1 <= (FStar_List.length args)
                                 then
                                   let uu____81582 =
                                     FStar_Util.first_N n1 args  in
                                   (match uu____81582 with
                                    | (prefix1,rest) ->
                                        let prefixAsMLTypes =
                                          FStar_List.map
                                            (fun uu____81687  ->
                                               match uu____81687 with
                                               | (x,uu____81695) ->
                                                   term_as_mlty g x) prefix1
                                           in
                                        let t2 =
                                          instantiate (vars, t1)
                                            prefixAsMLTypes
                                           in
                                        (FStar_Extraction_ML_UEnv.debug g
                                           (fun uu____81707  ->
                                              let uu____81708 =
                                                FStar_Syntax_Print.term_to_string
                                                  head2
                                                 in
                                              let uu____81710 =
                                                FStar_Syntax_Print.args_to_string
                                                  prefix1
                                                 in
                                              let uu____81712 =
                                                let uu____81714 =
                                                  FStar_List.map
                                                    (FStar_Extraction_ML_Code.string_of_mlty
                                                       g.FStar_Extraction_ML_UEnv.currentModule)
                                                    prefixAsMLTypes
                                                   in
                                                FStar_All.pipe_right
                                                  uu____81714
                                                  (FStar_String.concat ", ")
                                                 in
                                              let uu____81724 =
                                                FStar_Extraction_ML_Code.string_of_mlty
                                                  g.FStar_Extraction_ML_UEnv.currentModule
                                                  t2
                                                 in
                                              FStar_Util.print4
                                                "@@@looked up %s, instantiated with [%s] translated to [%s], got %s\n"
                                                uu____81708 uu____81710
                                                uu____81712 uu____81724);
                                         (let mk_tapp e ty_args =
                                            match ty_args with
                                            | [] -> e
                                            | uu____81742 ->
                                                let uu___2234_81745 = e  in
                                                {
                                                  FStar_Extraction_ML_Syntax.expr
                                                    =
                                                    (FStar_Extraction_ML_Syntax.MLE_TApp
                                                       (e, ty_args));
                                                  FStar_Extraction_ML_Syntax.mlty
                                                    =
                                                    (uu___2234_81745.FStar_Extraction_ML_Syntax.mlty);
                                                  FStar_Extraction_ML_Syntax.loc
                                                    =
                                                    (uu___2234_81745.FStar_Extraction_ML_Syntax.loc)
                                                }
                                             in
                                          let head3 =
                                            match head_ml.FStar_Extraction_ML_Syntax.expr
                                            with
                                            | FStar_Extraction_ML_Syntax.MLE_Name
                                                uu____81749 ->
                                                let uu___2240_81750 =
                                                  mk_tapp head_ml
                                                    prefixAsMLTypes
                                                   in
                                                {
                                                  FStar_Extraction_ML_Syntax.expr
                                                    =
                                                    (uu___2240_81750.FStar_Extraction_ML_Syntax.expr);
                                                  FStar_Extraction_ML_Syntax.mlty
                                                    = t2;
                                                  FStar_Extraction_ML_Syntax.loc
                                                    =
                                                    (uu___2240_81750.FStar_Extraction_ML_Syntax.loc)
                                                }
                                            | FStar_Extraction_ML_Syntax.MLE_Var
                                                uu____81751 ->
                                                let uu___2240_81753 =
                                                  mk_tapp head_ml
                                                    prefixAsMLTypes
                                                   in
                                                {
                                                  FStar_Extraction_ML_Syntax.expr
                                                    =
                                                    (uu___2240_81753.FStar_Extraction_ML_Syntax.expr);
                                                  FStar_Extraction_ML_Syntax.mlty
                                                    = t2;
                                                  FStar_Extraction_ML_Syntax.loc
                                                    =
                                                    (uu___2240_81753.FStar_Extraction_ML_Syntax.loc)
                                                }
                                            | FStar_Extraction_ML_Syntax.MLE_App
                                                (head3,{
                                                         FStar_Extraction_ML_Syntax.expr
                                                           =
                                                           FStar_Extraction_ML_Syntax.MLE_Const
                                                           (FStar_Extraction_ML_Syntax.MLC_Unit
                                                           );
                                                         FStar_Extraction_ML_Syntax.mlty
                                                           = uu____81755;
                                                         FStar_Extraction_ML_Syntax.loc
                                                           = uu____81756;_}::[])
                                                ->
                                                FStar_All.pipe_right
                                                  (FStar_Extraction_ML_Syntax.MLE_App
                                                     ((let uu___2251_81762 =
                                                         mk_tapp head3
                                                           prefixAsMLTypes
                                                          in
                                                       {
                                                         FStar_Extraction_ML_Syntax.expr
                                                           =
                                                           (uu___2251_81762.FStar_Extraction_ML_Syntax.expr);
                                                         FStar_Extraction_ML_Syntax.mlty
                                                           =
                                                           (FStar_Extraction_ML_Syntax.MLTY_Fun
                                                              (FStar_Extraction_ML_Syntax.ml_unit_ty,
                                                                FStar_Extraction_ML_Syntax.E_PURE,
                                                                t2));
                                                         FStar_Extraction_ML_Syntax.loc
                                                           =
                                                           (uu___2251_81762.FStar_Extraction_ML_Syntax.loc)
                                                       }),
                                                       [FStar_Extraction_ML_Syntax.ml_unit]))
                                                  (FStar_Extraction_ML_Syntax.with_ty
                                                     t2)
                                            | uu____81763 ->
                                                failwith
                                                  "Impossible: Unexpected head term"
                                             in
                                          (head3, t2, rest))))
                                 else err_uninst g head2 (vars, t1) top
                              in
                           (match uu____81503 with
                            | (head_ml1,head_t,args1) ->
                                (match args1 with
                                 | [] ->
                                     let uu____81829 =
                                       maybe_eta_data_and_project_record g
                                         qual head_t head_ml1
                                        in
                                     (uu____81829,
                                       FStar_Extraction_ML_Syntax.E_PURE,
                                       head_t)
                                 | uu____81830 ->
                                     extract_app_maybe_projector qual
                                       head_ml1
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         head_t) args1)))
                  | FStar_Syntax_Syntax.Tm_fvar uu____81839 ->
                      let uu____81840 =
                        let uu____81861 =
                          FStar_Extraction_ML_UEnv.lookup_term g head2  in
                        match uu____81861 with
                        | (FStar_Util.Inr exp_b,q) ->
                            (FStar_Extraction_ML_UEnv.debug g
                               (fun uu____81900  ->
                                  let uu____81901 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  let uu____81903 =
                                    FStar_Extraction_ML_Code.string_of_mlexpr
                                      g.FStar_Extraction_ML_UEnv.currentModule
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_expr
                                     in
                                  let uu____81905 =
                                    FStar_Extraction_ML_Code.string_of_mlty
                                      g.FStar_Extraction_ML_UEnv.currentModule
                                      (FStar_Pervasives_Native.snd
                                         exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme)
                                     in
                                  let uu____81907 =
                                    FStar_Util.string_of_bool
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok
                                     in
                                  FStar_Util.print4
                                    "@@@looked up %s: got %s at %s (inst_ok=%s)\n"
                                    uu____81901 uu____81903 uu____81905
                                    uu____81907);
                             (((exp_b.FStar_Extraction_ML_UEnv.exp_b_expr),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok)),
                               q))
                        | uu____81934 -> failwith "FIXME Ty"  in
                      (match uu____81840 with
                       | ((head_ml,(vars,t1),inst_ok),qual) ->
                           let has_typ_apps =
                             match args with
                             | (a,uu____82010)::uu____82011 -> is_type g a
                             | uu____82038 -> false  in
                           let uu____82050 =
                             match vars with
                             | uu____82079::uu____82080 when
                                 (Prims.op_Negation has_typ_apps) && inst_ok
                                 -> (head_ml, t1, args)
                             | uu____82094 ->
                                 let n1 = FStar_List.length vars  in
                                 if n1 <= (FStar_List.length args)
                                 then
                                   let uu____82129 =
                                     FStar_Util.first_N n1 args  in
                                   (match uu____82129 with
                                    | (prefix1,rest) ->
                                        let prefixAsMLTypes =
                                          FStar_List.map
                                            (fun uu____82234  ->
                                               match uu____82234 with
                                               | (x,uu____82242) ->
                                                   term_as_mlty g x) prefix1
                                           in
                                        let t2 =
                                          instantiate (vars, t1)
                                            prefixAsMLTypes
                                           in
                                        (FStar_Extraction_ML_UEnv.debug g
                                           (fun uu____82254  ->
                                              let uu____82255 =
                                                FStar_Syntax_Print.term_to_string
                                                  head2
                                                 in
                                              let uu____82257 =
                                                FStar_Syntax_Print.args_to_string
                                                  prefix1
                                                 in
                                              let uu____82259 =
                                                let uu____82261 =
                                                  FStar_List.map
                                                    (FStar_Extraction_ML_Code.string_of_mlty
                                                       g.FStar_Extraction_ML_UEnv.currentModule)
                                                    prefixAsMLTypes
                                                   in
                                                FStar_All.pipe_right
                                                  uu____82261
                                                  (FStar_String.concat ", ")
                                                 in
                                              let uu____82271 =
                                                FStar_Extraction_ML_Code.string_of_mlty
                                                  g.FStar_Extraction_ML_UEnv.currentModule
                                                  t2
                                                 in
                                              FStar_Util.print4
                                                "@@@looked up %s, instantiated with [%s] translated to [%s], got %s\n"
                                                uu____82255 uu____82257
                                                uu____82259 uu____82271);
                                         (let mk_tapp e ty_args =
                                            match ty_args with
                                            | [] -> e
                                            | uu____82289 ->
                                                let uu___2234_82292 = e  in
                                                {
                                                  FStar_Extraction_ML_Syntax.expr
                                                    =
                                                    (FStar_Extraction_ML_Syntax.MLE_TApp
                                                       (e, ty_args));
                                                  FStar_Extraction_ML_Syntax.mlty
                                                    =
                                                    (uu___2234_82292.FStar_Extraction_ML_Syntax.mlty);
                                                  FStar_Extraction_ML_Syntax.loc
                                                    =
                                                    (uu___2234_82292.FStar_Extraction_ML_Syntax.loc)
                                                }
                                             in
                                          let head3 =
                                            match head_ml.FStar_Extraction_ML_Syntax.expr
                                            with
                                            | FStar_Extraction_ML_Syntax.MLE_Name
                                                uu____82296 ->
                                                let uu___2240_82297 =
                                                  mk_tapp head_ml
                                                    prefixAsMLTypes
                                                   in
                                                {
                                                  FStar_Extraction_ML_Syntax.expr
                                                    =
                                                    (uu___2240_82297.FStar_Extraction_ML_Syntax.expr);
                                                  FStar_Extraction_ML_Syntax.mlty
                                                    = t2;
                                                  FStar_Extraction_ML_Syntax.loc
                                                    =
                                                    (uu___2240_82297.FStar_Extraction_ML_Syntax.loc)
                                                }
                                            | FStar_Extraction_ML_Syntax.MLE_Var
                                                uu____82298 ->
                                                let uu___2240_82300 =
                                                  mk_tapp head_ml
                                                    prefixAsMLTypes
                                                   in
                                                {
                                                  FStar_Extraction_ML_Syntax.expr
                                                    =
                                                    (uu___2240_82300.FStar_Extraction_ML_Syntax.expr);
                                                  FStar_Extraction_ML_Syntax.mlty
                                                    = t2;
                                                  FStar_Extraction_ML_Syntax.loc
                                                    =
                                                    (uu___2240_82300.FStar_Extraction_ML_Syntax.loc)
                                                }
                                            | FStar_Extraction_ML_Syntax.MLE_App
                                                (head3,{
                                                         FStar_Extraction_ML_Syntax.expr
                                                           =
                                                           FStar_Extraction_ML_Syntax.MLE_Const
                                                           (FStar_Extraction_ML_Syntax.MLC_Unit
                                                           );
                                                         FStar_Extraction_ML_Syntax.mlty
                                                           = uu____82302;
                                                         FStar_Extraction_ML_Syntax.loc
                                                           = uu____82303;_}::[])
                                                ->
                                                FStar_All.pipe_right
                                                  (FStar_Extraction_ML_Syntax.MLE_App
                                                     ((let uu___2251_82309 =
                                                         mk_tapp head3
                                                           prefixAsMLTypes
                                                          in
                                                       {
                                                         FStar_Extraction_ML_Syntax.expr
                                                           =
                                                           (uu___2251_82309.FStar_Extraction_ML_Syntax.expr);
                                                         FStar_Extraction_ML_Syntax.mlty
                                                           =
                                                           (FStar_Extraction_ML_Syntax.MLTY_Fun
                                                              (FStar_Extraction_ML_Syntax.ml_unit_ty,
                                                                FStar_Extraction_ML_Syntax.E_PURE,
                                                                t2));
                                                         FStar_Extraction_ML_Syntax.loc
                                                           =
                                                           (uu___2251_82309.FStar_Extraction_ML_Syntax.loc)
                                                       }),
                                                       [FStar_Extraction_ML_Syntax.ml_unit]))
                                                  (FStar_Extraction_ML_Syntax.with_ty
                                                     t2)
                                            | uu____82310 ->
                                                failwith
                                                  "Impossible: Unexpected head term"
                                             in
                                          (head3, t2, rest))))
                                 else err_uninst g head2 (vars, t1) top
                              in
                           (match uu____82050 with
                            | (head_ml1,head_t,args1) ->
                                (match args1 with
                                 | [] ->
                                     let uu____82376 =
                                       maybe_eta_data_and_project_record g
                                         qual head_t head_ml1
                                        in
                                     (uu____82376,
                                       FStar_Extraction_ML_Syntax.E_PURE,
                                       head_t)
                                 | uu____82377 ->
                                     extract_app_maybe_projector qual
                                       head_ml1
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         head_t) args1)))
                  | uu____82386 ->
                      let uu____82387 = term_as_mlexpr g head2  in
                      (match uu____82387 with
                       | (head3,f,t1) ->
                           extract_app_maybe_projector
                             FStar_Pervasives_Native.None head3 (f, t1) args)
                   in
                let uu____82403 = is_type g t  in
                if uu____82403
                then
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
                else
                  (let uu____82414 =
                     let uu____82415 = FStar_Syntax_Util.un_uinst head1  in
                     uu____82415.FStar_Syntax_Syntax.n  in
                   match uu____82414 with
                   | FStar_Syntax_Syntax.Tm_fvar fv ->
                       let uu____82425 =
                         FStar_Extraction_ML_UEnv.try_lookup_fv g fv  in
                       (match uu____82425 with
                        | FStar_Pervasives_Native.None  ->
                            (FStar_Extraction_ML_Syntax.ml_unit,
                              FStar_Extraction_ML_Syntax.E_PURE,
                              FStar_Extraction_ML_Syntax.MLTY_Erased)
                        | uu____82434 -> extract_app_with_instantiations ())
                   | uu____82437 -> extract_app_with_instantiations ()))
       | FStar_Syntax_Syntax.Tm_ascribed (e0,(tc,uu____82440),f) ->
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
           let uu____82508 = check_term_as_mlexpr g e0 f1 t1  in
           (match uu____82508 with | (e,t2) -> (e, f1, t2))
       | FStar_Syntax_Syntax.Tm_let ((is_rec,lbs),e') ->
           let top_level = FStar_Syntax_Syntax.is_top_level lbs  in
           let uu____82543 =
             if is_rec
             then FStar_Syntax_Subst.open_let_rec lbs e'
             else
               (let uu____82559 = FStar_Syntax_Syntax.is_top_level lbs  in
                if uu____82559
                then (lbs, e')
                else
                  (let lb = FStar_List.hd lbs  in
                   let x =
                     let uu____82574 =
                       FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                     FStar_Syntax_Syntax.freshen_bv uu____82574  in
                   let lb1 =
                     let uu___2302_82576 = lb  in
                     {
                       FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                       FStar_Syntax_Syntax.lbunivs =
                         (uu___2302_82576.FStar_Syntax_Syntax.lbunivs);
                       FStar_Syntax_Syntax.lbtyp =
                         (uu___2302_82576.FStar_Syntax_Syntax.lbtyp);
                       FStar_Syntax_Syntax.lbeff =
                         (uu___2302_82576.FStar_Syntax_Syntax.lbeff);
                       FStar_Syntax_Syntax.lbdef =
                         (uu___2302_82576.FStar_Syntax_Syntax.lbdef);
                       FStar_Syntax_Syntax.lbattrs =
                         (uu___2302_82576.FStar_Syntax_Syntax.lbattrs);
                       FStar_Syntax_Syntax.lbpos =
                         (uu___2302_82576.FStar_Syntax_Syntax.lbpos)
                     }  in
                   let e'1 =
                     FStar_Syntax_Subst.subst
                       [FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x)] e'
                      in
                   ([lb1], e'1)))
              in
           (match uu____82543 with
            | (lbs1,e'1) ->
                let lbs2 =
                  if top_level
                  then
                    FStar_All.pipe_right lbs1
                      (FStar_List.map
                         (fun lb  ->
                            let tcenv =
                              let uu____82610 =
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
                                uu____82610
                               in
                            let lbdef =
                              let uu____82625 = FStar_Options.ml_ish ()  in
                              if uu____82625
                              then lb.FStar_Syntax_Syntax.lbdef
                              else
                                (let norm_call uu____82637 =
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
                                 let uu____82638 =
                                   (FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug tcenv)
                                      (FStar_Options.Other "Extraction"))
                                     ||
                                     (FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug tcenv)
                                        (FStar_Options.Other "ExtractNorm"))
                                    in
                                 if uu____82638
                                 then
                                   ((let uu____82648 =
                                       FStar_Syntax_Print.lbname_to_string
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     let uu____82650 =
                                       FStar_Syntax_Print.term_to_string
                                         lb.FStar_Syntax_Syntax.lbdef
                                        in
                                     FStar_Util.print2
                                       "Starting to normalize top-level let %s)\n\tlbdef=%s"
                                       uu____82648 uu____82650);
                                    (let a =
                                       let uu____82656 =
                                         let uu____82658 =
                                           FStar_Syntax_Print.lbname_to_string
                                             lb.FStar_Syntax_Syntax.lbname
                                            in
                                         FStar_Util.format1
                                           "###(Time to normalize top-level let %s)"
                                           uu____82658
                                          in
                                       FStar_Util.measure_execution_time
                                         uu____82656 norm_call
                                        in
                                     (let uu____82664 =
                                        FStar_Syntax_Print.term_to_string a
                                         in
                                      FStar_Util.print1 "Normalized to %s\n"
                                        uu____82664);
                                     a))
                                 else norm_call ())
                               in
                            let uu___2320_82669 = lb  in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___2320_82669.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___2320_82669.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp =
                                (uu___2320_82669.FStar_Syntax_Syntax.lbtyp);
                              FStar_Syntax_Syntax.lbeff =
                                (uu___2320_82669.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = lbdef;
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___2320_82669.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___2320_82669.FStar_Syntax_Syntax.lbpos)
                            }))
                  else lbs1  in
                let check_lb env uu____82722 =
                  match uu____82722 with
                  | (nm,(_lbname,f,(_t,(targs,polytype)),add_unit,e)) ->
                      let env1 =
                        FStar_List.fold_left
                          (fun env1  ->
                             fun uu____82878  ->
                               match uu____82878 with
                               | (a,uu____82886) ->
                                   FStar_Extraction_ML_UEnv.extend_ty env1 a
                                     FStar_Pervasives_Native.None) env targs
                         in
                      let expected_t = FStar_Pervasives_Native.snd polytype
                         in
                      let uu____82892 =
                        check_term_as_mlexpr env1 e f expected_t  in
                      (match uu____82892 with
                       | (e1,ty) ->
                           let uu____82903 =
                             maybe_promote_effect e1 f expected_t  in
                           (match uu____82903 with
                            | (e2,f1) ->
                                let meta =
                                  match (f1, ty) with
                                  | (FStar_Extraction_ML_Syntax.E_PURE
                                     ,FStar_Extraction_ML_Syntax.MLTY_Erased
                                     ) -> [FStar_Extraction_ML_Syntax.Erased]
                                  | (FStar_Extraction_ML_Syntax.E_GHOST
                                     ,FStar_Extraction_ML_Syntax.MLTY_Erased
                                     ) -> [FStar_Extraction_ML_Syntax.Erased]
                                  | uu____82915 -> []  in
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
                let uu____82946 =
                  FStar_List.fold_right
                    (fun lb  ->
                       fun uu____83043  ->
                         match uu____83043 with
                         | (env,lbs4) ->
                             let uu____83177 = lb  in
                             (match uu____83177 with
                              | (lbname,uu____83228,(t1,(uu____83230,polytype)),add_unit,uu____83233)
                                  ->
                                  let uu____83248 =
                                    FStar_Extraction_ML_UEnv.extend_lb env
                                      lbname t1 polytype add_unit true
                                     in
                                  (match uu____83248 with
                                   | (env1,nm,uu____83289) ->
                                       (env1, ((nm, lb) :: lbs4))))) lbs3
                    (g, [])
                   in
                (match uu____82946 with
                 | (env_body,lbs4) ->
                     let env_def = if is_rec then env_body else g  in
                     let lbs5 =
                       FStar_All.pipe_right lbs4
                         (FStar_List.map (check_lb env_def))
                        in
                     let e'_rng = e'1.FStar_Syntax_Syntax.pos  in
                     let uu____83568 = term_as_mlexpr env_body e'1  in
                     (match uu____83568 with
                      | (e'2,f',t') ->
                          let f =
                            let uu____83585 =
                              let uu____83588 =
                                FStar_List.map FStar_Pervasives_Native.fst
                                  lbs5
                                 in
                              f' :: uu____83588  in
                            FStar_Extraction_ML_Util.join_l e'_rng
                              uu____83585
                             in
                          let is_rec1 =
                            if is_rec = true
                            then FStar_Extraction_ML_Syntax.Rec
                            else FStar_Extraction_ML_Syntax.NonRec  in
                          let uu____83601 =
                            let uu____83602 =
                              let uu____83603 =
                                let uu____83604 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    lbs5
                                   in
                                (is_rec1, uu____83604)  in
                              mk_MLE_Let top_level uu____83603 e'2  in
                            let uu____83613 =
                              FStar_Extraction_ML_Util.mlloc_of_range
                                t.FStar_Syntax_Syntax.pos
                               in
                            FStar_Extraction_ML_Syntax.with_ty_loc t'
                              uu____83602 uu____83613
                             in
                          (uu____83601, f, t'))))
       | FStar_Syntax_Syntax.Tm_match (scrutinee,pats) ->
           let uu____83652 = term_as_mlexpr g scrutinee  in
           (match uu____83652 with
            | (e,f_e,t_e) ->
                let uu____83668 = check_pats_for_ite pats  in
                (match uu____83668 with
                 | (b,then_e,else_e) ->
                     let no_lift x t1 = x  in
                     if b
                     then
                       (match (then_e, else_e) with
                        | (FStar_Pervasives_Native.Some
                           then_e1,FStar_Pervasives_Native.Some else_e1) ->
                            let uu____83733 = term_as_mlexpr g then_e1  in
                            (match uu____83733 with
                             | (then_mle,f_then,t_then) ->
                                 let uu____83749 = term_as_mlexpr g else_e1
                                    in
                                 (match uu____83749 with
                                  | (else_mle,f_else,t_else) ->
                                      let uu____83765 =
                                        let uu____83776 =
                                          type_leq g t_then t_else  in
                                        if uu____83776
                                        then (t_else, no_lift)
                                        else
                                          (let uu____83797 =
                                             type_leq g t_else t_then  in
                                           if uu____83797
                                           then (t_then, no_lift)
                                           else
                                             (FStar_Extraction_ML_Syntax.MLTY_Top,
                                               FStar_Extraction_ML_Syntax.apply_obj_repr))
                                         in
                                      (match uu____83765 with
                                       | (t_branch,maybe_lift1) ->
                                           let uu____83844 =
                                             let uu____83845 =
                                               let uu____83846 =
                                                 let uu____83855 =
                                                   maybe_lift1 then_mle
                                                     t_then
                                                    in
                                                 let uu____83856 =
                                                   let uu____83859 =
                                                     maybe_lift1 else_mle
                                                       t_else
                                                      in
                                                   FStar_Pervasives_Native.Some
                                                     uu____83859
                                                    in
                                                 (e, uu____83855,
                                                   uu____83856)
                                                  in
                                               FStar_Extraction_ML_Syntax.MLE_If
                                                 uu____83846
                                                in
                                             FStar_All.pipe_left
                                               (FStar_Extraction_ML_Syntax.with_ty
                                                  t_branch) uu____83845
                                              in
                                           let uu____83862 =
                                             FStar_Extraction_ML_Util.join
                                               then_e1.FStar_Syntax_Syntax.pos
                                               f_then f_else
                                              in
                                           (uu____83844, uu____83862,
                                             t_branch))))
                        | uu____83863 ->
                            failwith
                              "ITE pats matched but then and else expressions not found?")
                     else
                       (let uu____83881 =
                          FStar_All.pipe_right pats
                            (FStar_Util.fold_map
                               (fun compat  ->
                                  fun br  ->
                                    let uu____83980 =
                                      FStar_Syntax_Subst.open_branch br  in
                                    match uu____83980 with
                                    | (pat,when_opt,branch1) ->
                                        let uu____84025 =
                                          extract_pat g pat t_e
                                            term_as_mlexpr
                                           in
                                        (match uu____84025 with
                                         | (env,p,pat_t_compat) ->
                                             let uu____84087 =
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
                                                   let uu____84110 =
                                                     term_as_mlexpr env w  in
                                                   (match uu____84110 with
                                                    | (w1,f_w,t_w) ->
                                                        let w2 =
                                                          maybe_coerce w_pos
                                                            env w1 t_w
                                                            FStar_Extraction_ML_Syntax.ml_bool_ty
                                                           in
                                                        ((FStar_Pervasives_Native.Some
                                                            w2), f_w))
                                                in
                                             (match uu____84087 with
                                              | (when_opt1,f_when) ->
                                                  let uu____84160 =
                                                    term_as_mlexpr env
                                                      branch1
                                                     in
                                                  (match uu____84160 with
                                                   | (mlbranch,f_branch,t_branch)
                                                       ->
                                                       let uu____84195 =
                                                         FStar_All.pipe_right
                                                           p
                                                           (FStar_List.map
                                                              (fun
                                                                 uu____84272 
                                                                 ->
                                                                 match uu____84272
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
                                                         uu____84195)))))
                               true)
                           in
                        match uu____83881 with
                        | (pat_t_compat,mlbranches) ->
                            let mlbranches1 = FStar_List.flatten mlbranches
                               in
                            let e1 =
                              if pat_t_compat
                              then e
                              else
                                (FStar_Extraction_ML_UEnv.debug g
                                   (fun uu____84443  ->
                                      let uu____84444 =
                                        FStar_Extraction_ML_Code.string_of_mlexpr
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          e
                                         in
                                      let uu____84446 =
                                        FStar_Extraction_ML_Code.string_of_mlty
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          t_e
                                         in
                                      FStar_Util.print2
                                        "Coercing scrutinee %s from type %s because pattern type is incompatible\n"
                                        uu____84444 uu____84446);
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty t_e)
                                   (FStar_Extraction_ML_Syntax.MLE_Coerce
                                      (e, t_e,
                                        FStar_Extraction_ML_Syntax.MLTY_Top)))
                               in
                            (match mlbranches1 with
                             | [] ->
                                 let uu____84473 =
                                   let uu____84474 =
                                     FStar_Syntax_Syntax.lid_as_fv
                                       FStar_Parser_Const.failwith_lid
                                       FStar_Syntax_Syntax.delta_constant
                                       FStar_Pervasives_Native.None
                                      in
                                   FStar_Extraction_ML_UEnv.lookup_fv g
                                     uu____84474
                                    in
                                 (match uu____84473 with
                                  | {
                                      FStar_Extraction_ML_UEnv.exp_b_name =
                                        uu____84481;
                                      FStar_Extraction_ML_UEnv.exp_b_expr =
                                        fw;
                                      FStar_Extraction_ML_UEnv.exp_b_tscheme
                                        = uu____84483;
                                      FStar_Extraction_ML_UEnv.exp_b_inst_ok
                                        = uu____84484;_}
                                      ->
                                      let uu____84487 =
                                        let uu____84488 =
                                          let uu____84489 =
                                            let uu____84496 =
                                              let uu____84499 =
                                                FStar_All.pipe_left
                                                  (FStar_Extraction_ML_Syntax.with_ty
                                                     FStar_Extraction_ML_Syntax.ml_string_ty)
                                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                                     (FStar_Extraction_ML_Syntax.MLC_String
                                                        "unreachable"))
                                                 in
                                              [uu____84499]  in
                                            (fw, uu____84496)  in
                                          FStar_Extraction_ML_Syntax.MLE_App
                                            uu____84489
                                           in
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             FStar_Extraction_ML_Syntax.ml_int_ty)
                                          uu____84488
                                         in
                                      (uu____84487,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        FStar_Extraction_ML_Syntax.ml_int_ty))
                             | (uu____84503,uu____84504,(uu____84505,f_first,t_first))::rest
                                 ->
                                 let uu____84565 =
                                   FStar_List.fold_left
                                     (fun uu____84607  ->
                                        fun uu____84608  ->
                                          match (uu____84607, uu____84608)
                                          with
                                          | ((topt,f),(uu____84665,uu____84666,
                                                       (uu____84667,f_branch,t_branch)))
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
                                                    let uu____84723 =
                                                      type_leq g t1 t_branch
                                                       in
                                                    if uu____84723
                                                    then
                                                      FStar_Pervasives_Native.Some
                                                        t_branch
                                                    else
                                                      (let uu____84730 =
                                                         type_leq g t_branch
                                                           t1
                                                          in
                                                       if uu____84730
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
                                 (match uu____84565 with
                                  | (topt,f_match) ->
                                      let mlbranches2 =
                                        FStar_All.pipe_right mlbranches1
                                          (FStar_List.map
                                             (fun uu____84828  ->
                                                match uu____84828 with
                                                | (p,(wopt,uu____84857),
                                                   (b1,uu____84859,t1)) ->
                                                    let b2 =
                                                      match topt with
                                                      | FStar_Pervasives_Native.None
                                                           ->
                                                          FStar_Extraction_ML_Syntax.apply_obj_repr
                                                            b1 t1
                                                      | FStar_Pervasives_Native.Some
                                                          uu____84878 -> b1
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
                                      let uu____84883 =
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             t_match)
                                          (FStar_Extraction_ML_Syntax.MLE_Match
                                             (e1, mlbranches2))
                                         in
                                      (uu____84883, f_match, t_match)))))))

let (ind_discriminator_body :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlmodule1)
  =
  fun env  ->
    fun discName  ->
      fun constrName  ->
        let uu____84910 =
          let uu____84915 =
            FStar_TypeChecker_Env.lookup_lid
              env.FStar_Extraction_ML_UEnv.env_tcenv discName
             in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____84915  in
        match uu____84910 with
        | (uu____84940,fstar_disc_type) ->
            let wildcards =
              let uu____84950 =
                let uu____84951 = FStar_Syntax_Subst.compress fstar_disc_type
                   in
                uu____84951.FStar_Syntax_Syntax.n  in
              match uu____84950 with
              | FStar_Syntax_Syntax.Tm_arrow (binders,uu____84962) ->
                  let uu____84983 =
                    FStar_All.pipe_right binders
                      (FStar_List.filter
                         (fun uu___620_85017  ->
                            match uu___620_85017 with
                            | (uu____85025,FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____85026)) ->
                                true
                            | uu____85031 -> false))
                     in
                  FStar_All.pipe_right uu____84983
                    (FStar_List.map
                       (fun uu____85067  ->
                          let uu____85074 = fresh "_"  in
                          (uu____85074, FStar_Extraction_ML_Syntax.MLTY_Top)))
              | uu____85078 -> failwith "Discriminator must be a function"
               in
            let mlid = fresh "_discr_"  in
            let targ = FStar_Extraction_ML_Syntax.MLTY_Top  in
            let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top  in
            let discrBody =
              let uu____85093 =
                let uu____85094 =
                  let uu____85106 =
                    let uu____85107 =
                      let uu____85108 =
                        let uu____85123 =
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty targ)
                            (FStar_Extraction_ML_Syntax.MLE_Name ([], mlid))
                           in
                        let uu____85129 =
                          let uu____85140 =
                            let uu____85149 =
                              let uu____85150 =
                                let uu____85157 =
                                  FStar_Extraction_ML_Syntax.mlpath_of_lident
                                    constrName
                                   in
                                (uu____85157,
                                  [FStar_Extraction_ML_Syntax.MLP_Wild])
                                 in
                              FStar_Extraction_ML_Syntax.MLP_CTor uu____85150
                               in
                            let uu____85160 =
                              FStar_All.pipe_left
                                (FStar_Extraction_ML_Syntax.with_ty
                                   FStar_Extraction_ML_Syntax.ml_bool_ty)
                                (FStar_Extraction_ML_Syntax.MLE_Const
                                   (FStar_Extraction_ML_Syntax.MLC_Bool true))
                               in
                            (uu____85149, FStar_Pervasives_Native.None,
                              uu____85160)
                             in
                          let uu____85164 =
                            let uu____85175 =
                              let uu____85184 =
                                FStar_All.pipe_left
                                  (FStar_Extraction_ML_Syntax.with_ty
                                     FStar_Extraction_ML_Syntax.ml_bool_ty)
                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                     (FStar_Extraction_ML_Syntax.MLC_Bool
                                        false))
                                 in
                              (FStar_Extraction_ML_Syntax.MLP_Wild,
                                FStar_Pervasives_Native.None, uu____85184)
                               in
                            [uu____85175]  in
                          uu____85140 :: uu____85164  in
                        (uu____85123, uu____85129)  in
                      FStar_Extraction_ML_Syntax.MLE_Match uu____85108  in
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.ml_bool_ty) uu____85107
                     in
                  ((FStar_List.append wildcards [(mlid, targ)]), uu____85106)
                   in
                FStar_Extraction_ML_Syntax.MLE_Fun uu____85094  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty disc_ty) uu____85093
               in
            let uu____85245 =
              let uu____85246 =
                let uu____85249 =
                  let uu____85250 =
                    FStar_Extraction_ML_UEnv.convIdent
                      discName.FStar_Ident.ident
                     in
                  {
                    FStar_Extraction_ML_Syntax.mllb_name = uu____85250;
                    FStar_Extraction_ML_Syntax.mllb_tysc =
                      FStar_Pervasives_Native.None;
                    FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                    FStar_Extraction_ML_Syntax.mllb_def = discrBody;
                    FStar_Extraction_ML_Syntax.mllb_meta = [];
                    FStar_Extraction_ML_Syntax.print_typ = false
                  }  in
                [uu____85249]  in
              (FStar_Extraction_ML_Syntax.NonRec, uu____85246)  in
            FStar_Extraction_ML_Syntax.MLM_Let uu____85245
  