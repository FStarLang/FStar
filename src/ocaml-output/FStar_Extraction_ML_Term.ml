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
  
let record_fields :
  'Auu____440 .
    FStar_Ident.ident Prims.list ->
      'Auu____440 Prims.list -> (Prims.string * 'Auu____440) Prims.list
  =
  fun fs  ->
    fun vs  ->
      FStar_List.map2 (fun f  -> fun e  -> ((f.FStar_Ident.idText), e)) fs vs
  
let fail :
  'Auu____491 .
    FStar_Range.range ->
      (FStar_Errors.raw_error * Prims.string) -> 'Auu____491
  = fun r  -> fun err  -> FStar_Errors.raise_error err r 
let err_ill_typed_application :
  'Auu____527 'Auu____528 .
    FStar_Extraction_ML_UEnv.uenv ->
      FStar_Syntax_Syntax.term ->
        FStar_Extraction_ML_Syntax.mlexpr ->
          (FStar_Syntax_Syntax.term * 'Auu____527) Prims.list ->
            FStar_Extraction_ML_Syntax.mlty -> 'Auu____528
  =
  fun env  ->
    fun t  ->
      fun mlhead  ->
        fun args  ->
          fun ty  ->
            let uu____706 =
              let uu____712 =
                let uu____714 = FStar_Syntax_Print.term_to_string t  in
                let uu____716 =
                  FStar_Extraction_ML_Code.string_of_mlexpr
                    env.FStar_Extraction_ML_UEnv.currentModule mlhead
                   in
                let uu____718 =
                  FStar_Extraction_ML_Code.string_of_mlty
                    env.FStar_Extraction_ML_UEnv.currentModule ty
                   in
                let uu____720 =
                  let uu____722 =
                    FStar_All.pipe_right args
                      (FStar_List.map
                         (fun uu____751  ->
                            match uu____751 with
                            | (x,uu____762) ->
                                FStar_Syntax_Print.term_to_string x))
                     in
                  FStar_All.pipe_right uu____722 (FStar_String.concat " ")
                   in
                FStar_Util.format4
                  "Ill-typed application: source application is %s \n translated prefix to %s at type %s\n remaining args are %s\n"
                  uu____714 uu____716 uu____718 uu____720
                 in
              (FStar_Errors.Fatal_IllTyped, uu____712)  in
            fail t.FStar_Syntax_Syntax.pos uu____706
  
let err_ill_typed_erasure :
  'Auu____787 .
    FStar_Extraction_ML_UEnv.uenv ->
      FStar_Range.range -> FStar_Extraction_ML_Syntax.mlty -> 'Auu____787
  =
  fun env  ->
    fun pos  ->
      fun ty  ->
        let uu____921 =
          let uu____927 =
            let uu____929 =
              FStar_Extraction_ML_Code.string_of_mlty
                env.FStar_Extraction_ML_UEnv.currentModule ty
               in
            FStar_Util.format1
              "Erased value found where a value of type %s was expected"
              uu____929
             in
          (FStar_Errors.Fatal_IllTyped, uu____927)  in
        fail pos uu____921
  
let err_value_restriction :
  'Auu____938 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> 'Auu____938
  =
  fun t  ->
    let uu____956 =
      let uu____962 =
        let uu____964 = FStar_Syntax_Print.tag_of_term t  in
        let uu____966 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format2
          "Refusing to generalize because of the value restriction: (%s) %s"
          uu____964 uu____966
         in
      (FStar_Errors.Fatal_ValueRestriction, uu____962)  in
    fail t.FStar_Syntax_Syntax.pos uu____956
  
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
            let uu____1126 =
              let uu____1132 =
                let uu____1134 = FStar_Syntax_Print.term_to_string t  in
                let uu____1136 =
                  FStar_Extraction_ML_Code.string_of_mlty
                    env.FStar_Extraction_ML_UEnv.currentModule ty
                   in
                let uu____1138 = FStar_Extraction_ML_Util.eff_to_string f0
                   in
                let uu____1140 = FStar_Extraction_ML_Util.eff_to_string f1
                   in
                FStar_Util.format4
                  "for expression %s of type %s, Expected effect %s; got effect %s"
                  uu____1134 uu____1136 uu____1138 uu____1140
                 in
              (FStar_Errors.Warning_ExtractionUnexpectedEffect, uu____1132)
               in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____1126
  
let (effect_as_etag :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Ident.lident -> FStar_Extraction_ML_Syntax.e_tag)
  =
  let cache = FStar_Util.smap_create (Prims.parse_int "20")  in
  let rec delta_norm_eff g l =
    let uu____1369 = FStar_Util.smap_try_find cache l.FStar_Ident.str  in
    match uu____1369 with
    | FStar_Pervasives_Native.Some l1 -> l1
    | FStar_Pervasives_Native.None  ->
        let res =
          let uu____1406 =
            FStar_TypeChecker_Env.lookup_effect_abbrev
              g.FStar_Extraction_ML_UEnv.env_tcenv
              [FStar_Syntax_Syntax.U_zero] l
             in
          match uu____1406 with
          | FStar_Pervasives_Native.None  -> l
          | FStar_Pervasives_Native.Some (uu____1429,c) ->
              delta_norm_eff g (FStar_Syntax_Util.comp_effect_name c)
           in
        (FStar_Util.smap_add cache l.FStar_Ident.str res; res)
     in
  fun g  ->
    fun l  ->
      let l1 = delta_norm_eff g l  in
      let uu____1526 =
        FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid  in
      if uu____1526
      then FStar_Extraction_ML_Syntax.E_PURE
      else
        (let uu____1531 =
           FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GHOST_lid  in
         if uu____1531
         then FStar_Extraction_ML_Syntax.E_GHOST
         else
           (let ed_opt =
              FStar_TypeChecker_Env.effect_decl_opt
                g.FStar_Extraction_ML_UEnv.env_tcenv l1
               in
            match ed_opt with
            | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                let uu____1637 =
                  FStar_TypeChecker_Env.is_reifiable_effect
                    g.FStar_Extraction_ML_UEnv.env_tcenv
                    ed.FStar_Syntax_Syntax.mname
                   in
                if uu____1637
                then FStar_Extraction_ML_Syntax.E_PURE
                else FStar_Extraction_ML_Syntax.E_IMPURE
            | FStar_Pervasives_Native.None  ->
                FStar_Extraction_ML_Syntax.E_IMPURE))
  
let rec (is_arity :
  FStar_Extraction_ML_UEnv.uenv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t  in
      let uu____1815 =
        let uu____1816 = FStar_Syntax_Subst.compress t1  in
        uu____1816.FStar_Syntax_Syntax.n  in
      match uu____1815 with
      | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____1830 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_ascribed uu____1863 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_meta uu____1912 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____1930 = FStar_Syntax_Util.unfold_lazy i  in
          is_arity env uu____1930
      | FStar_Syntax_Syntax.Tm_uvar uu____1939 -> false
      | FStar_Syntax_Syntax.Tm_constant uu____1961 -> false
      | FStar_Syntax_Syntax.Tm_name uu____1963 -> false
      | FStar_Syntax_Syntax.Tm_quoted uu____1970 -> false
      | FStar_Syntax_Syntax.Tm_bvar uu____1984 -> false
      | FStar_Syntax_Syntax.Tm_type uu____1991 -> true
      | FStar_Syntax_Syntax.Tm_arrow (uu____1993,c) ->
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
           | FStar_Pervasives_Native.Some (uu____2062,t2) -> is_arity env t2)
      | FStar_Syntax_Syntax.Tm_app uu____2080 ->
          let uu____2105 = FStar_Syntax_Util.head_and_args t1  in
          (match uu____2105 with | (head1,uu____2132) -> is_arity env head1)
      | FStar_Syntax_Syntax.Tm_uinst (head1,uu____2174) -> is_arity env head1
      | FStar_Syntax_Syntax.Tm_refine (x,uu____2188) ->
          is_arity env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_abs (uu____2211,body,uu____2213) ->
          is_arity env body
      | FStar_Syntax_Syntax.Tm_let (uu____2270,body) -> is_arity env body
      | FStar_Syntax_Syntax.Tm_match (uu____2312,branches) ->
          (match branches with
           | (uu____2381,uu____2382,e)::uu____2384 -> is_arity env e
           | uu____2475 -> false)
  
let rec (is_type_aux :
  FStar_Extraction_ML_UEnv.uenv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____2652 ->
          let uu____2683 =
            let uu____2685 = FStar_Syntax_Print.tag_of_term t1  in
            FStar_Util.format1 "Impossible: %s" uu____2685  in
          failwith uu____2683
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____2689 =
            let uu____2691 = FStar_Syntax_Print.tag_of_term t1  in
            FStar_Util.format1 "Impossible: %s" uu____2691  in
          failwith uu____2689
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____2700 = FStar_Syntax_Util.unfold_lazy i  in
          is_type_aux env uu____2700
      | FStar_Syntax_Syntax.Tm_constant uu____2709 -> false
      | FStar_Syntax_Syntax.Tm_type uu____2711 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____2713 -> true
      | FStar_Syntax_Syntax.Tm_arrow uu____2730 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.failwith_lid ->
          false
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Extraction_ML_UEnv.is_type_name env fv
      | FStar_Syntax_Syntax.Tm_uvar
          ({ FStar_Syntax_Syntax.ctx_uvar_head = uu____2764;
             FStar_Syntax_Syntax.ctx_uvar_gamma = uu____2765;
             FStar_Syntax_Syntax.ctx_uvar_binders = uu____2766;
             FStar_Syntax_Syntax.ctx_uvar_typ = t2;
             FStar_Syntax_Syntax.ctx_uvar_reason = uu____2768;
             FStar_Syntax_Syntax.ctx_uvar_should_check = uu____2769;
             FStar_Syntax_Syntax.ctx_uvar_range = uu____2770;
             FStar_Syntax_Syntax.ctx_uvar_meta = uu____2771;_},s)
          ->
          let uu____2847 = FStar_Syntax_Subst.subst' s t2  in
          is_arity env uu____2847
      | FStar_Syntax_Syntax.Tm_bvar
          { FStar_Syntax_Syntax.ppname = uu____2856;
            FStar_Syntax_Syntax.index = uu____2857;
            FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_name
          { FStar_Syntax_Syntax.ppname = uu____2868;
            FStar_Syntax_Syntax.index = uu____2869;
            FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____2881,uu____2882) ->
          is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____2964) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____2979) ->
          let uu____3036 = FStar_Syntax_Subst.open_term bs body  in
          (match uu____3036 with
           | (uu____3046,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
          let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
          let uu____3135 =
            let uu____3144 =
              let uu____3145 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____3145]  in
            FStar_Syntax_Subst.open_term uu____3144 body  in
          (match uu____3135 with
           | (uu____3180,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_let ((uu____3190,lbs),body) ->
          let uu____3239 = FStar_Syntax_Subst.open_let_rec lbs body  in
          (match uu____3239 with
           | (uu____3258,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_match (uu____3286,branches) ->
          (match branches with
           | b::uu____3356 ->
               let uu____3434 = FStar_Syntax_Subst.open_branch b  in
               (match uu____3434 with
                | (uu____3436,uu____3437,e) -> is_type_aux env e)
           | uu____3477 -> false)
      | FStar_Syntax_Syntax.Tm_quoted uu____3506 -> false
      | FStar_Syntax_Syntax.Tm_meta (t2,uu____3521) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_app (head1,uu____3535) ->
          is_type_aux env head1
  
let (is_type :
  FStar_Extraction_ML_UEnv.uenv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      FStar_Extraction_ML_UEnv.debug env
        (fun uu____3718  ->
           let uu____3719 = FStar_Syntax_Print.tag_of_term t  in
           let uu____3721 = FStar_Syntax_Print.term_to_string t  in
           FStar_Util.print2 "checking is_type (%s) %s\n" uu____3719
             uu____3721);
      (let b = is_type_aux env t  in
       FStar_Extraction_ML_UEnv.debug env
         (fun uu____3730  ->
            if b
            then
              let uu____3732 = FStar_Syntax_Print.term_to_string t  in
              let uu____3734 = FStar_Syntax_Print.tag_of_term t  in
              FStar_Util.print2 "yes, is_type %s (%s)\n" uu____3732
                uu____3734
            else
              (let uu____3739 = FStar_Syntax_Print.term_to_string t  in
               let uu____3741 = FStar_Syntax_Print.tag_of_term t  in
               FStar_Util.print2 "not a type %s (%s)\n" uu____3739 uu____3741));
       b)
  
let is_type_binder :
  'Auu____3751 .
    FStar_Extraction_ML_UEnv.uenv ->
      (FStar_Syntax_Syntax.bv * 'Auu____3751) -> Prims.bool
  =
  fun env  ->
    fun x  ->
      is_arity env (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
  
let (is_constructor : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3919 =
      let uu____3920 = FStar_Syntax_Subst.compress t  in
      uu____3920.FStar_Syntax_Syntax.n  in
    match uu____3919 with
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____3932;
          FStar_Syntax_Syntax.fv_delta = uu____3933;
          FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
            (FStar_Syntax_Syntax.Data_ctor );_}
        -> true
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____3935;
          FStar_Syntax_Syntax.fv_delta = uu____3936;
          FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
            (FStar_Syntax_Syntax.Record_ctor uu____3937);_}
        -> true
    | uu____3951 -> false
  
let rec (is_fstar_value : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3968 =
      let uu____3969 = FStar_Syntax_Subst.compress t  in
      uu____3969.FStar_Syntax_Syntax.n  in
    match uu____3968 with
    | FStar_Syntax_Syntax.Tm_constant uu____3981 -> true
    | FStar_Syntax_Syntax.Tm_bvar uu____3983 -> true
    | FStar_Syntax_Syntax.Tm_fvar uu____3990 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____3995 -> true
    | FStar_Syntax_Syntax.Tm_app (head1,args) ->
        let uu____4073 = is_constructor head1  in
        if uu____4073
        then
          FStar_All.pipe_right args
            (FStar_List.for_all
               (fun uu____4103  ->
                  match uu____4103 with
                  | (te,uu____4116) -> is_fstar_value te))
        else false
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____4133) -> is_fstar_value t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____4147,uu____4148) ->
        is_fstar_value t1
    | uu____4229 -> false
  
let rec (is_ml_value : FStar_Extraction_ML_Syntax.mlexpr -> Prims.bool) =
  fun e  ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_Const uu____4245 -> true
    | FStar_Extraction_ML_Syntax.MLE_Var uu____4247 -> true
    | FStar_Extraction_ML_Syntax.MLE_Name uu____4250 -> true
    | FStar_Extraction_ML_Syntax.MLE_Fun uu____4252 -> true
    | FStar_Extraction_ML_Syntax.MLE_CTor (uu____4268,exps) ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Tuple exps ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Record (uu____4292,fields) ->
        FStar_Util.for_all
          (fun uu____4331  ->
             match uu____4331 with | (uu____4341,e1) -> is_ml_value e1)
          fields
    | FStar_Extraction_ML_Syntax.MLE_TApp (h,uu____4352) -> is_ml_value h
    | uu____4363 -> false
  
let (fresh : Prims.string -> Prims.string) =
  let c = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun x  ->
    FStar_Util.incr c;
    (let uu____4381 =
       let uu____4383 = FStar_ST.op_Bang c  in
       FStar_Util.string_of_int uu____4383  in
     Prims.op_Hat x uu____4381)
  
let (normalize_abs : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t0  ->
    let rec aux bs t copt =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_abs (bs',body,copt1) ->
          aux (FStar_List.append bs bs') body copt1
      | uu____4587 ->
          let e' = FStar_Syntax_Util.unascribe t1  in
          let uu____4597 = FStar_Syntax_Util.is_fun e'  in
          if uu____4597
          then aux bs e' copt
          else FStar_Syntax_Util.abs bs e' copt
       in
    aux [] t0 FStar_Pervasives_Native.None
  
let (unit_binder : FStar_Syntax_Syntax.binder) =
  let uu____4627 =
    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
      FStar_Syntax_Syntax.t_unit
     in
  FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____4627 
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
      (let uu____4805 = FStar_List.hd l  in
       match uu____4805 with
       | (p1,w1,e1) ->
           let uu____4880 =
             let uu____4897 = FStar_List.tl l  in FStar_List.hd uu____4897
              in
           (match uu____4880 with
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
                 | uu____5109 -> def)))
  
let (instantiate_tyscheme :
  FStar_Extraction_ML_Syntax.mltyscheme ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty)
  = fun s  -> fun args  -> FStar_Extraction_ML_Util.subst s args 
let (instantiate_maybe_partial :
  FStar_Extraction_ML_Syntax.mlexpr ->
    FStar_Extraction_ML_Syntax.mltyscheme ->
      FStar_Extraction_ML_Syntax.mlty Prims.list ->
        (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag
          * FStar_Extraction_ML_Syntax.mlty))
  =
  fun e  ->
    fun s  ->
      fun tyargs  ->
        let uu____5189 = s  in
        match uu____5189 with
        | (vars,t) ->
            let n_vars = FStar_List.length vars  in
            let n_args = FStar_List.length tyargs  in
            if n_args = n_vars
            then
              (if n_args = (Prims.parse_int "0")
               then (e, FStar_Extraction_ML_Syntax.E_PURE, t)
               else
                 (let ts = instantiate_tyscheme (vars, t) tyargs  in
                  let tapp =
                    let uu___365_5239 = e  in
                    {
                      FStar_Extraction_ML_Syntax.expr =
                        (FStar_Extraction_ML_Syntax.MLE_TApp (e, tyargs));
                      FStar_Extraction_ML_Syntax.mlty = ts;
                      FStar_Extraction_ML_Syntax.loc =
                        (uu___365_5239.FStar_Extraction_ML_Syntax.loc)
                    }  in
                  (tapp, FStar_Extraction_ML_Syntax.E_PURE, ts)))
            else
              if n_args < n_vars
              then
                (let extra_tyargs =
                   let uu____5269 = FStar_Util.first_N n_args vars  in
                   match uu____5269 with
                   | (uu____5283,rest_vars) ->
                       FStar_All.pipe_right rest_vars
                         (FStar_List.map
                            (fun uu____5304  ->
                               FStar_Extraction_ML_Syntax.MLTY_Erased))
                    in
                 let tyargs1 = FStar_List.append tyargs extra_tyargs  in
                 let ts = instantiate_tyscheme (vars, t) tyargs1  in
                 let tapp =
                   let uu___376_5317 = e  in
                   {
                     FStar_Extraction_ML_Syntax.expr =
                       (FStar_Extraction_ML_Syntax.MLE_TApp (e, tyargs1));
                     FStar_Extraction_ML_Syntax.mlty = ts;
                     FStar_Extraction_ML_Syntax.loc =
                       (uu___376_5317.FStar_Extraction_ML_Syntax.loc)
                   }  in
                 let t1 =
                   FStar_List.fold_left
                     (fun out  ->
                        fun t1  ->
                          FStar_Extraction_ML_Syntax.MLTY_Fun
                            (t1, FStar_Extraction_ML_Syntax.E_PURE, out)) ts
                     extra_tyargs
                    in
                 let f =
                   let vs_ts =
                     FStar_List.map
                       (fun t2  ->
                          let uu____5357 = fresh "t"  in (uu____5357, t2))
                       extra_tyargs
                      in
                   FStar_All.pipe_left
                     (FStar_Extraction_ML_Syntax.with_ty t1)
                     (FStar_Extraction_ML_Syntax.MLE_Fun (vs_ts, tapp))
                    in
                 (f, FStar_Extraction_ML_Syntax.E_PURE, t1))
              else
                failwith
                  "Impossible: instantiate_maybe_partial called with too many arguments"
  
let (eta_expand :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun t  ->
    fun e  ->
      let uu____5412 = FStar_Extraction_ML_Util.doms_and_cod t  in
      match uu____5412 with
      | (ts,r) ->
          if ts = []
          then e
          else
            (let vs = FStar_List.map (fun uu____5442  -> fresh "a") ts  in
             let vs_ts = FStar_List.zip vs ts  in
             let vs_es =
               let uu____5459 = FStar_List.zip vs ts  in
               FStar_List.map
                 (fun uu____5479  ->
                    match uu____5479 with
                    | (v1,t1) ->
                        FStar_Extraction_ML_Syntax.with_ty t1
                          (FStar_Extraction_ML_Syntax.MLE_Var v1)) uu____5459
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
      let uu____5658 = FStar_Extraction_ML_Util.doms_and_cod t  in
      match uu____5658 with
      | (ts,r) ->
          let body r1 =
            let r2 =
              let uu____5684 = FStar_Extraction_ML_Util.udelta_unfold g r1
                 in
              match uu____5684 with
              | FStar_Pervasives_Native.None  -> r1
              | FStar_Pervasives_Native.Some r2 -> r2  in
            match r2 with
            | FStar_Extraction_ML_Syntax.MLTY_Erased  ->
                FStar_Extraction_ML_Syntax.ml_unit
            | FStar_Extraction_ML_Syntax.MLTY_Top  ->
                FStar_Extraction_ML_Syntax.apply_obj_repr
                  FStar_Extraction_ML_Syntax.ml_unit
                  FStar_Extraction_ML_Syntax.MLTY_Erased
            | uu____5691 ->
                FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty r2)
                  (FStar_Extraction_ML_Syntax.MLE_Coerce
                     (FStar_Extraction_ML_Syntax.ml_unit,
                       FStar_Extraction_ML_Syntax.MLTY_Erased, r2))
             in
          if ts = []
          then body r
          else
            (let vs = FStar_List.map (fun uu____5712  -> fresh "a") ts  in
             let vs_ts = FStar_List.zip vs ts  in
             let uu____5723 =
               let uu____5724 =
                 let uu____5739 = body r  in (vs_ts, uu____5739)  in
               FStar_Extraction_ML_Syntax.MLE_Fun uu____5724  in
             FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t)
               uu____5723)
  
let (maybe_eta_expand :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun expect  ->
    fun e  ->
      let uu____5779 =
        (FStar_Options.ml_no_eta_expand_coertions ()) ||
          (let uu____5782 = FStar_Options.codegen ()  in
           uu____5782 = (FStar_Pervasives_Native.Some FStar_Options.Kremlin))
         in
      if uu____5779 then e else eta_expand expect e
  
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
            | uu____6008 ->
                FStar_Extraction_ML_Syntax.MLE_Fun ([binder], body)
             in
          let rec aux e1 ty1 expect1 =
            let coerce_branch uu____6087 =
              match uu____6087 with
              | (pat,w,b) ->
                  let uu____6135 = aux b ty1 expect1  in (pat, w, uu____6135)
               in
            match ((e1.FStar_Extraction_ML_Syntax.expr), ty1, expect1) with
            | (FStar_Extraction_ML_Syntax.MLE_Fun
               (arg::rest,body),FStar_Extraction_ML_Syntax.MLTY_Fun
               (t0,uu____6157,t1),FStar_Extraction_ML_Syntax.MLTY_Fun
               (s0,uu____6160,s1)) ->
                let body1 =
                  match rest with
                  | [] -> body
                  | uu____6207 ->
                      FStar_Extraction_ML_Syntax.with_ty t1
                        (FStar_Extraction_ML_Syntax.MLE_Fun (rest, body))
                   in
                let body2 = aux body1 t1 s1  in
                let uu____6232 = type_leq g s0 t0  in
                if uu____6232
                then
                  FStar_Extraction_ML_Syntax.with_ty expect1
                    (mk_fun arg body2)
                else
                  (let lb =
                     let uu____6253 =
                       let uu____6260 =
                         let uu____6261 =
                           let uu____6271 =
                             FStar_All.pipe_left
                               (FStar_Extraction_ML_Syntax.with_ty s0)
                               (FStar_Extraction_ML_Syntax.MLE_Var
                                  (FStar_Pervasives_Native.fst arg))
                              in
                           (uu____6271, s0, t0)  in
                         FStar_Extraction_ML_Syntax.MLE_Coerce uu____6261  in
                       FStar_Extraction_ML_Syntax.with_ty t0 uu____6260  in
                     {
                       FStar_Extraction_ML_Syntax.mllb_name =
                         (FStar_Pervasives_Native.fst arg);
                       FStar_Extraction_ML_Syntax.mllb_tysc =
                         (FStar_Pervasives_Native.Some ([], t0));
                       FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                       FStar_Extraction_ML_Syntax.mllb_def = uu____6253;
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
               (lbs,body),uu____6338,uu____6339) ->
                let uu____6370 =
                  let uu____6371 =
                    let uu____6391 = aux body ty1 expect1  in
                    (lbs, uu____6391)  in
                  FStar_Extraction_ML_Syntax.MLE_Let uu____6371  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____6370
            | (FStar_Extraction_ML_Syntax.MLE_Match
               (s,branches),uu____6418,uu____6419) ->
                let uu____6458 =
                  let uu____6459 =
                    let uu____6483 = FStar_List.map coerce_branch branches
                       in
                    (s, uu____6483)  in
                  FStar_Extraction_ML_Syntax.MLE_Match uu____6459  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____6458
            | (FStar_Extraction_ML_Syntax.MLE_If
               (s,b1,b2_opt),uu____6553,uu____6554) ->
                let uu____6577 =
                  let uu____6578 =
                    let uu____6596 = aux b1 ty1 expect1  in
                    let uu____6603 =
                      FStar_Util.map_opt b2_opt
                        (fun b2  -> aux b2 ty1 expect1)
                       in
                    (s, uu____6596, uu____6603)  in
                  FStar_Extraction_ML_Syntax.MLE_If uu____6578  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____6577
            | (FStar_Extraction_ML_Syntax.MLE_Seq es,uu____6635,uu____6636)
                ->
                let uu____6642 = FStar_Util.prefix es  in
                (match uu____6642 with
                 | (prefix1,last1) ->
                     let uu____6679 =
                       let uu____6680 =
                         let uu____6686 =
                           let uu____6692 = aux last1 ty1 expect1  in
                           [uu____6692]  in
                         FStar_List.append prefix1 uu____6686  in
                       FStar_Extraction_ML_Syntax.MLE_Seq uu____6680  in
                     FStar_All.pipe_left
                       (FStar_Extraction_ML_Syntax.with_ty expect1)
                       uu____6679)
            | (FStar_Extraction_ML_Syntax.MLE_Try
               (s,branches),uu____6713,uu____6714) ->
                let uu____6753 =
                  let uu____6754 =
                    let uu____6778 = FStar_List.map coerce_branch branches
                       in
                    (s, uu____6778)  in
                  FStar_Extraction_ML_Syntax.MLE_Try uu____6754  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____6753
            | uu____6845 ->
                FStar_Extraction_ML_Syntax.with_ty expect1
                  (FStar_Extraction_ML_Syntax.MLE_Coerce (e1, ty1, expect1))
             in
          aux e ty expect
  
let maybe_coerce :
  'Auu____6868 .
    'Auu____6868 ->
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
            let uu____7022 =
              type_leq_c g (FStar_Pervasives_Native.Some e) ty1 expect  in
            match uu____7022 with
            | (true ,FStar_Pervasives_Native.Some e') -> e'
            | uu____7053 ->
                (match ty1 with
                 | FStar_Extraction_ML_Syntax.MLTY_Erased  ->
                     default_value_for_ty g expect
                 | uu____7067 ->
                     let uu____7068 =
                       let uu____7070 =
                         FStar_Extraction_ML_Util.erase_effect_annotations
                           ty1
                          in
                       let uu____7071 =
                         FStar_Extraction_ML_Util.erase_effect_annotations
                           expect
                          in
                       type_leq g uu____7070 uu____7071  in
                     if uu____7068
                     then
                       (FStar_Extraction_ML_UEnv.debug g
                          (fun uu____7080  ->
                             let uu____7081 =
                               FStar_Extraction_ML_Code.string_of_mlexpr
                                 g.FStar_Extraction_ML_UEnv.currentModule e
                                in
                             let uu____7083 =
                               FStar_Extraction_ML_Code.string_of_mlty
                                 g.FStar_Extraction_ML_UEnv.currentModule ty1
                                in
                             FStar_Util.print2
                               "\n Effect mismatch on type of %s : %s\n"
                               uu____7081 uu____7083);
                        e)
                     else
                       (FStar_Extraction_ML_UEnv.debug g
                          (fun uu____7093  ->
                             let uu____7094 =
                               FStar_Extraction_ML_Code.string_of_mlexpr
                                 g.FStar_Extraction_ML_UEnv.currentModule e
                                in
                             let uu____7096 =
                               FStar_Extraction_ML_Code.string_of_mlty
                                 g.FStar_Extraction_ML_UEnv.currentModule ty1
                                in
                             let uu____7098 =
                               FStar_Extraction_ML_Code.string_of_mlty
                                 g.FStar_Extraction_ML_UEnv.currentModule
                                 expect
                                in
                             FStar_Util.print3
                               "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n"
                               uu____7094 uu____7096 uu____7098);
                        (let uu____7101 = apply_coercion g e ty1 expect  in
                         maybe_eta_expand expect uu____7101)))
  
let (bv_as_mlty :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun bv  ->
      let uu____7247 = FStar_Extraction_ML_UEnv.lookup_bv g bv  in
      match uu____7247 with
      | FStar_Util.Inl ty_b -> ty_b.FStar_Extraction_ML_UEnv.ty_b_ty
      | uu____7257 -> FStar_Extraction_ML_Syntax.MLTY_Top
  
let (extraction_norm_steps : FStar_TypeChecker_Env.step Prims.list) =
  [FStar_TypeChecker_Env.AllowUnboundUniverses;
  FStar_TypeChecker_Env.EraseUniverses;
  FStar_TypeChecker_Env.Inlining;
  FStar_TypeChecker_Env.Eager_unfolding false;
  FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
  FStar_TypeChecker_Env.Primops;
  FStar_TypeChecker_Env.Unascribe;
  FStar_TypeChecker_Env.ForExtraction] 
let (comp_no_args :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____7292 -> c
    | FStar_Syntax_Syntax.GTotal uu____7305 -> c
    | FStar_Syntax_Syntax.Comp ct ->
        let effect_args =
          FStar_List.map
            (fun uu____7362  ->
               match uu____7362 with
               | (uu____7385,aq) -> (FStar_Syntax_Syntax.t_unit, aq))
            ct.FStar_Syntax_Syntax.effect_args
           in
        let ct1 =
          let uu___538_7420 = ct  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___538_7420.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___538_7420.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ =
              (uu___538_7420.FStar_Syntax_Syntax.result_typ);
            FStar_Syntax_Syntax.effect_args = effect_args;
            FStar_Syntax_Syntax.flags =
              (uu___538_7420.FStar_Syntax_Syntax.flags)
          }  in
        let c1 =
          let uu___541_7442 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
            FStar_Syntax_Syntax.pos = (uu___541_7442.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___541_7442.FStar_Syntax_Syntax.vars)
          }  in
        c1
  
let rec (translate_term_to_mlty :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun t0  ->
      let arg_as_mlty g1 uu____7806 =
        match uu____7806 with
        | (a,uu____7877) ->
            let uu____7890 = is_type g1 a  in
            if uu____7890
            then translate_term_to_mlty g1 a
            else FStar_Extraction_ML_UEnv.erasedContent
         in
      let fv_app_as_mlty g1 fv args =
        let uu____8035 =
          let uu____8037 = FStar_Extraction_ML_UEnv.is_fv_type g1 fv  in
          Prims.op_Negation uu____8037  in
        if uu____8035
        then FStar_Extraction_ML_Syntax.MLTY_Top
        else
          (let uu____8042 =
             let uu____8066 =
               FStar_TypeChecker_Env.lookup_lid
                 g1.FStar_Extraction_ML_UEnv.env_tcenv
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             match uu____8066 with
             | ((uu____8106,fvty),uu____8108) ->
                 let fvty1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Env.UnfoldUntil
                        FStar_Syntax_Syntax.delta_constant]
                     g1.FStar_Extraction_ML_UEnv.env_tcenv fvty
                    in
                 FStar_Syntax_Util.arrow_formals fvty1
              in
           match uu____8042 with
           | (formals,uu____8135) ->
               let mlargs = FStar_List.map (arg_as_mlty g1) args  in
               let mlargs1 =
                 let n_args = FStar_List.length args  in
                 if (FStar_List.length formals) > n_args
                 then
                   let uu____8219 = FStar_Util.first_N n_args formals  in
                   match uu____8219 with
                   | (uu____8263,rest) ->
                       let uu____8317 =
                         FStar_List.map
                           (fun uu____8332  ->
                              FStar_Extraction_ML_UEnv.erasedContent) rest
                          in
                       FStar_List.append mlargs uu____8317
                 else mlargs  in
               let nm =
                 let uu____8347 =
                   FStar_Extraction_ML_UEnv.maybe_mangle_type_projector g1 fv
                    in
                 match uu____8347 with
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
        | FStar_Syntax_Syntax.Tm_type uu____8503 ->
            FStar_Extraction_ML_Syntax.MLTY_Erased
        | FStar_Syntax_Syntax.Tm_bvar uu____8504 ->
            let uu____8510 =
              let uu____8512 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____8512
               in
            failwith uu____8510
        | FStar_Syntax_Syntax.Tm_delayed uu____8515 ->
            let uu____8546 =
              let uu____8548 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____8548
               in
            failwith uu____8546
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____8551 =
              let uu____8553 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____8553
               in
            failwith uu____8551
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____8561 = FStar_Syntax_Util.unfold_lazy i  in
            translate_term_to_mlty env uu____8561
        | FStar_Syntax_Syntax.Tm_constant uu____8570 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_quoted uu____8571 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_uvar uu____8584 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_meta (t2,uu____8606) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____8619;
               FStar_Syntax_Syntax.index = uu____8620;
               FStar_Syntax_Syntax.sort = t2;_},uu____8622)
            -> translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_uinst (t2,uu____8650) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____8664,uu____8665) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
        | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv []
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let uu____8808 = FStar_Syntax_Subst.open_comp bs c  in
            (match uu____8808 with
             | (bs1,c1) ->
                 let uu____8827 = binders_as_ml_binders env bs1  in
                 (match uu____8827 with
                  | (mlbs,env1) ->
                      let t_ret =
                        let eff =
                          FStar_TypeChecker_Env.norm_eff_name
                            env1.FStar_Extraction_ML_UEnv.env_tcenv
                            (FStar_Syntax_Util.comp_effect_name c1)
                           in
                        let c2 = comp_no_args c1  in
                        let uu____9053 =
                          let uu____9080 =
                            FStar_TypeChecker_Env.effect_decl_opt
                              env1.FStar_Extraction_ML_UEnv.env_tcenv eff
                             in
                          FStar_Util.must uu____9080  in
                        match uu____9053 with
                        | (ed,qualifiers) ->
                            let uu____9181 =
                              FStar_TypeChecker_Env.is_reifiable_effect
                                g.FStar_Extraction_ML_UEnv.env_tcenv
                                ed.FStar_Syntax_Syntax.mname
                               in
                            if uu____9181
                            then
                              let t2 =
                                FStar_TypeChecker_Env.reify_comp
                                  env1.FStar_Extraction_ML_UEnv.env_tcenv c2
                                  FStar_Syntax_Syntax.U_unknown
                                 in
                              (FStar_Extraction_ML_UEnv.debug env1
                                 (fun uu____9197  ->
                                    let uu____9198 =
                                      FStar_Syntax_Print.comp_to_string c2
                                       in
                                    let uu____9200 =
                                      FStar_Syntax_Print.term_to_string t2
                                       in
                                    FStar_Util.print2
                                      "Translating comp type %s as %s\n"
                                      uu____9198 uu____9200);
                               (let res = translate_term_to_mlty env1 t2  in
                                FStar_Extraction_ML_UEnv.debug env1
                                  (fun uu____9209  ->
                                     let uu____9210 =
                                       FStar_Syntax_Print.comp_to_string c2
                                        in
                                     let uu____9212 =
                                       FStar_Syntax_Print.term_to_string t2
                                        in
                                     let uu____9214 =
                                       FStar_Extraction_ML_Code.string_of_mlty
                                         env1.FStar_Extraction_ML_UEnv.currentModule
                                         res
                                        in
                                     FStar_Util.print3
                                       "Translated comp type %s as %s ... to %s\n"
                                       uu____9210 uu____9212 uu____9214);
                                res))
                            else
                              translate_term_to_mlty env1
                                (FStar_Syntax_Util.comp_result c2)
                         in
                      let erase =
                        effect_as_etag env1
                          (FStar_Syntax_Util.comp_effect_name c1)
                         in
                      let uu____9220 =
                        FStar_List.fold_right
                          (fun uu____9240  ->
                             fun uu____9241  ->
                               match (uu____9240, uu____9241) with
                               | ((uu____9264,t2),(tag,t')) ->
                                   (FStar_Extraction_ML_Syntax.E_PURE,
                                     (FStar_Extraction_ML_Syntax.MLTY_Fun
                                        (t2, tag, t')))) mlbs (erase, t_ret)
                         in
                      (match uu____9220 with | (uu____9279,t2) -> t2)))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let res =
              let uu____9324 =
                let uu____9325 = FStar_Syntax_Util.un_uinst head1  in
                uu____9325.FStar_Syntax_Syntax.n  in
              match uu____9324 with
              | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv args
              | FStar_Syntax_Syntax.Tm_app (head2,args') ->
                  let uu____9388 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_app
                         (head2, (FStar_List.append args' args)))
                      FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                     in
                  translate_term_to_mlty env uu____9388
              | uu____9429 -> FStar_Extraction_ML_UEnv.unknownType  in
            res
        | FStar_Syntax_Syntax.Tm_abs (bs,ty,uu____9432) ->
            let uu____9489 = FStar_Syntax_Subst.open_term bs ty  in
            (match uu____9489 with
             | (bs1,ty1) ->
                 let uu____9508 = binders_as_ml_binders env bs1  in
                 (match uu____9508 with
                  | (bts,env1) -> translate_term_to_mlty env1 ty1))
        | FStar_Syntax_Syntax.Tm_let uu____9713 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_match uu____9738 ->
            FStar_Extraction_ML_UEnv.unknownType
         in
      let rec is_top_ty t =
        match t with
        | FStar_Extraction_ML_Syntax.MLTY_Top  -> true
        | FStar_Extraction_ML_Syntax.MLTY_Named uu____9785 ->
            let uu____9792 = FStar_Extraction_ML_Util.udelta_unfold g t  in
            (match uu____9792 with
             | FStar_Pervasives_Native.None  -> false
             | FStar_Pervasives_Native.Some t1 -> is_top_ty t1)
        | uu____9798 -> false  in
      let uu____9800 =
        FStar_TypeChecker_Util.must_erase_for_extraction
          g.FStar_Extraction_ML_UEnv.env_tcenv t0
         in
      if uu____9800
      then FStar_Extraction_ML_Syntax.MLTY_Erased
      else
        (let mlt = aux g t0  in
         let uu____9806 = is_top_ty mlt  in
         if uu____9806 then FStar_Extraction_ML_Syntax.MLTY_Top else mlt)

and (binders_as_ml_binders :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.binders ->
      ((FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)
        Prims.list * FStar_Extraction_ML_UEnv.uenv))
  =
  fun g  ->
    fun bs  ->
      let uu____9942 =
        FStar_All.pipe_right bs
          (FStar_List.fold_left
             (fun uu____10185  ->
                fun b  ->
                  match uu____10185 with
                  | (ml_bs,env) ->
                      let uu____10472 = is_type_binder g b  in
                      if uu____10472
                      then
                        let b1 = FStar_Pervasives_Native.fst b  in
                        let env1 =
                          FStar_Extraction_ML_UEnv.extend_ty env b1
                            (FStar_Pervasives_Native.Some
                               FStar_Extraction_ML_Syntax.MLTY_Top)
                           in
                        let ml_b =
                          let uu____10690 =
                            FStar_Extraction_ML_UEnv.bv_as_ml_termvar b1  in
                          (uu____10690,
                            FStar_Extraction_ML_Syntax.ml_unit_ty)
                           in
                        ((ml_b :: ml_bs), env1)
                      else
                        (let b1 = FStar_Pervasives_Native.fst b  in
                         let t =
                           translate_term_to_mlty env
                             b1.FStar_Syntax_Syntax.sort
                            in
                         let uu____10785 =
                           FStar_Extraction_ML_UEnv.extend_bv env b1 
                             ([], t) false false false
                            in
                         match uu____10785 with
                         | (env1,b2,uu____10932) ->
                             let ml_b =
                               let uu____11067 =
                                 FStar_Extraction_ML_UEnv.removeTick b2  in
                               (uu____11067, t)  in
                             ((ml_b :: ml_bs), env1))) ([], g))
         in
      match uu____9942 with | (ml_bs,env) -> ((FStar_List.rev ml_bs), env)

let (term_as_mlty :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun t0  ->
      let t =
        FStar_TypeChecker_Normalize.normalize extraction_norm_steps
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
      | (FStar_Extraction_ML_Syntax.MLE_Seq es1,uu____11672) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (FStar_List.append es1 [e2])
      | (uu____11687,FStar_Extraction_ML_Syntax.MLE_Seq es2) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (e1 :: es2)
      | uu____11697 -> FStar_Extraction_ML_Syntax.MLE_Seq [e1; e2]
  
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
                    | uu____11770 when
                        (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
                          =
                          FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr
                        -> body.FStar_Extraction_ML_Syntax.expr
                    | uu____11771 ->
                        mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def
                          body)
             | uu____11772 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body))
        | uu____11790 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body)
  
let (resugar_pat :
  FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option ->
    FStar_Extraction_ML_Syntax.mlpattern ->
      FStar_Extraction_ML_Syntax.mlpattern)
  =
  fun q  ->
    fun p  ->
      match p with
      | FStar_Extraction_ML_Syntax.MLP_CTor (d,pats) ->
          let uu____11827 = FStar_Extraction_ML_Util.is_xtuple d  in
          (match uu____11827 with
           | FStar_Pervasives_Native.Some n1 ->
               FStar_Extraction_ML_Syntax.MLP_Tuple pats
           | uu____11834 ->
               (match q with
                | FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Record_ctor (ty,fns)) ->
                    let path =
                      FStar_List.map FStar_Ident.text_of_id ty.FStar_Ident.ns
                       in
                    let fs = record_fields fns pats  in
                    FStar_Extraction_ML_Syntax.MLP_Record (path, fs)
                | uu____11881 -> p))
      | uu____11884 -> p
  
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
                       (fun uu____12360  ->
                          let uu____12361 =
                            FStar_Extraction_ML_Code.string_of_mlty
                              g.FStar_Extraction_ML_UEnv.currentModule t'
                             in
                          let uu____12363 =
                            FStar_Extraction_ML_Code.string_of_mlty
                              g.FStar_Extraction_ML_UEnv.currentModule t
                             in
                          FStar_Util.print2
                            "Expected pattern type %s; got pattern type %s\n"
                            uu____12361 uu____12363)
                   else ();
                   ok)
               in
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int
                (c,swopt)) when
                let uu____12461 = FStar_Options.codegen ()  in
                uu____12461 <>
                  (FStar_Pervasives_Native.Some FStar_Options.Kremlin)
                ->
                let uu____12466 =
                  match swopt with
                  | FStar_Pervasives_Native.None  ->
                      let uu____12485 =
                        let uu____12492 =
                          let uu____12493 =
                            FStar_Extraction_ML_Util.mlconst_of_const
                              p.FStar_Syntax_Syntax.p
                              (FStar_Const.Const_int
                                 (c, FStar_Pervasives_Native.None))
                             in
                          FStar_Extraction_ML_Syntax.MLE_Const uu____12493
                           in
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.ml_int_ty)
                          uu____12492
                         in
                      (uu____12485, FStar_Extraction_ML_Syntax.ml_int_ty)
                  | FStar_Pervasives_Native.Some sw ->
                      let source_term =
                        FStar_ToSyntax_ToSyntax.desugar_machine_integer
                          (g.FStar_Extraction_ML_UEnv.env_tcenv).FStar_TypeChecker_Env.dsenv
                          c sw FStar_Range.dummyRange
                         in
                      let uu____12529 = term_as_mlexpr g source_term  in
                      (match uu____12529 with
                       | (mlterm,uu____12547,mlty) -> (mlterm, mlty))
                   in
                (match uu____12466 with
                 | (mlc,ml_ty) ->
                     let x = FStar_Extraction_ML_Syntax.gensym ()  in
                     let when_clause =
                       let uu____12652 =
                         let uu____12653 =
                           let uu____12666 =
                             let uu____12672 =
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty ml_ty)
                                 (FStar_Extraction_ML_Syntax.MLE_Var x)
                                in
                             [uu____12672; mlc]  in
                           (FStar_Extraction_ML_Util.prims_op_equality,
                             uu____12666)
                            in
                         FStar_Extraction_ML_Syntax.MLE_App uu____12653  in
                       FStar_All.pipe_left
                         (FStar_Extraction_ML_Syntax.with_ty
                            FStar_Extraction_ML_Syntax.ml_bool_ty)
                         uu____12652
                        in
                     let uu____12702 = ok ml_ty  in
                     (g,
                       (FStar_Pervasives_Native.Some
                          ((FStar_Extraction_ML_Syntax.MLP_Var x),
                            [when_clause])), uu____12702))
            | FStar_Syntax_Syntax.Pat_constant s ->
                let t =
                  FStar_TypeChecker_TcTerm.tc_constant
                    g.FStar_Extraction_ML_UEnv.env_tcenv
                    FStar_Range.dummyRange s
                   in
                let mlty = term_as_mlty g t  in
                let uu____12806 =
                  let uu____12818 =
                    let uu____12828 =
                      let uu____12829 =
                        FStar_Extraction_ML_Util.mlconst_of_const
                          p.FStar_Syntax_Syntax.p s
                         in
                      FStar_Extraction_ML_Syntax.MLP_Const uu____12829  in
                    (uu____12828, [])  in
                  FStar_Pervasives_Native.Some uu____12818  in
                let uu____12847 = ok mlty  in (g, uu____12806, uu____12847)
            | FStar_Syntax_Syntax.Pat_var x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort  in
                let uu____12927 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp
                   in
                (match uu____12927 with
                 | (g1,x1,uu____13080) ->
                     let uu____13209 = ok mlty  in
                     (g1,
                       (if imp
                        then FStar_Pervasives_Native.None
                        else
                          FStar_Pervasives_Native.Some
                            ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                       uu____13209))
            | FStar_Syntax_Syntax.Pat_wild x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort  in
                let uu____13329 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp
                   in
                (match uu____13329 with
                 | (g1,x1,uu____13482) ->
                     let uu____13611 = ok mlty  in
                     (g1,
                       (if imp
                        then FStar_Pervasives_Native.None
                        else
                          FStar_Pervasives_Native.Some
                            ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                       uu____13611))
            | FStar_Syntax_Syntax.Pat_dot_term uu____13724 ->
                (g, FStar_Pervasives_Native.None, true)
            | FStar_Syntax_Syntax.Pat_cons (f,pats) ->
                let uu____13853 =
                  let uu____13862 = FStar_Extraction_ML_UEnv.lookup_fv g f
                     in
                  match uu____13862 with
                  | { FStar_Extraction_ML_UEnv.exp_b_name = uu____13879;
                      FStar_Extraction_ML_UEnv.exp_b_expr =
                        {
                          FStar_Extraction_ML_Syntax.expr =
                            FStar_Extraction_ML_Syntax.MLE_Name n1;
                          FStar_Extraction_ML_Syntax.mlty = uu____13881;
                          FStar_Extraction_ML_Syntax.loc = uu____13882;_};
                      FStar_Extraction_ML_UEnv.exp_b_tscheme = ttys;
                      FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____13884;_}
                      -> (n1, ttys)
                  | uu____13891 -> failwith "Expected a constructor"  in
                (match uu____13853 with
                 | (d,tys) ->
                     let nTyVars =
                       FStar_List.length (FStar_Pervasives_Native.fst tys)
                        in
                     let uu____13994 = FStar_Util.first_N nTyVars pats  in
                     (match uu____13994 with
                      | (tysVarPats,restPats) ->
                          let f_ty_opt =
                            try
                              (fun uu___836_14181  ->
                                 match () with
                                 | () ->
                                     let mlty_args =
                                       FStar_All.pipe_right tysVarPats
                                         (FStar_List.map
                                            (fun uu____14212  ->
                                               match uu____14212 with
                                               | (p1,uu____14219) ->
                                                   (match p1.FStar_Syntax_Syntax.v
                                                    with
                                                    | FStar_Syntax_Syntax.Pat_dot_term
                                                        (uu____14222,t) ->
                                                        term_as_mlty g t
                                                    | uu____14246 ->
                                                        (FStar_Extraction_ML_UEnv.debug
                                                           g
                                                           (fun uu____14250 
                                                              ->
                                                              let uu____14251
                                                                =
                                                                FStar_Syntax_Print.pat_to_string
                                                                  p1
                                                                 in
                                                              FStar_Util.print1
                                                                "Pattern %s is not extractable"
                                                                uu____14251);
                                                         FStar_Exn.raise
                                                           Un_extractable))))
                                        in
                                     let f_ty =
                                       FStar_Extraction_ML_Util.subst tys
                                         mlty_args
                                        in
                                     let uu____14255 =
                                       FStar_Extraction_ML_Util.uncurry_mlty_fun
                                         f_ty
                                        in
                                     FStar_Pervasives_Native.Some uu____14255)
                                ()
                            with
                            | Un_extractable  -> FStar_Pervasives_Native.None
                             in
                          let uu____14284 =
                            FStar_Util.fold_map
                              (fun g1  ->
                                 fun uu____14445  ->
                                   match uu____14445 with
                                   | (p1,imp1) ->
                                       let uu____14588 =
                                         extract_one_pat true g1 p1
                                           FStar_Pervasives_Native.None
                                           term_as_mlexpr
                                          in
                                       (match uu____14588 with
                                        | (g2,p2,uu____14743) -> (g2, p2))) g
                              tysVarPats
                             in
                          (match uu____14284 with
                           | (g1,tyMLPats) ->
                               let uu____15179 =
                                 FStar_Util.fold_map
                                   (fun uu____15368  ->
                                      fun uu____15369  ->
                                        match (uu____15368, uu____15369) with
                                        | ((g2,f_ty_opt1),(p1,imp1)) ->
                                            let uu____15824 =
                                              match f_ty_opt1 with
                                              | FStar_Pervasives_Native.Some
                                                  (hd1::rest,res) ->
                                                  ((FStar_Pervasives_Native.Some
                                                      (rest, res)),
                                                    (FStar_Pervasives_Native.Some
                                                       hd1))
                                              | uu____15884 ->
                                                  (FStar_Pervasives_Native.None,
                                                    FStar_Pervasives_Native.None)
                                               in
                                            (match uu____15824 with
                                             | (f_ty_opt2,expected_ty) ->
                                                 let uu____16017 =
                                                   extract_one_pat false g2
                                                     p1 expected_ty
                                                     term_as_mlexpr
                                                    in
                                                 (match uu____16017 with
                                                  | (g3,p2,uu____16184) ->
                                                      ((g3, f_ty_opt2), p2))))
                                   (g1, f_ty_opt) restPats
                                  in
                               (match uu____15179 with
                                | ((g2,f_ty_opt1),restMLPats) ->
                                    let uu____16854 =
                                      let uu____16868 =
                                        FStar_All.pipe_right
                                          (FStar_List.append tyMLPats
                                             restMLPats)
                                          (FStar_List.collect
                                             (fun uu___0_16937  ->
                                                match uu___0_16937 with
                                                | FStar_Pervasives_Native.Some
                                                    x -> [x]
                                                | uu____16997 -> []))
                                         in
                                      FStar_All.pipe_right uu____16868
                                        FStar_List.split
                                       in
                                    (match uu____16854 with
                                     | (mlPats,when_clauses) ->
                                         let pat_ty_compat =
                                           match f_ty_opt1 with
                                           | FStar_Pervasives_Native.Some
                                               ([],t) -> ok t
                                           | uu____17156 -> false  in
                                         let uu____17166 =
                                           let uu____17178 =
                                             let uu____17188 =
                                               resugar_pat
                                                 f.FStar_Syntax_Syntax.fv_qual
                                                 (FStar_Extraction_ML_Syntax.MLP_CTor
                                                    (d, mlPats))
                                                in
                                             let uu____17191 =
                                               FStar_All.pipe_right
                                                 when_clauses
                                                 FStar_List.flatten
                                                in
                                             (uu____17188, uu____17191)  in
                                           FStar_Pervasives_Native.Some
                                             uu____17178
                                            in
                                         (g2, uu____17166, pat_ty_compat))))))
  
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
            let uu____17957 =
              extract_one_pat false g1 p1 expected_t1 term_as_mlexpr  in
            match uu____17957 with
            | (g2,FStar_Pervasives_Native.Some (x,v1),b) -> (g2, (x, v1), b)
            | uu____18339 ->
                failwith "Impossible: Unable to translate pattern"
             in
          let mk_when_clause whens =
            match whens with
            | [] -> FStar_Pervasives_Native.None
            | hd1::tl1 ->
                let uu____18538 =
                  FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd1
                    tl1
                   in
                FStar_Pervasives_Native.Some uu____18538
             in
          let uu____18554 =
            extract_one_pat1 g p (FStar_Pervasives_Native.Some expected_t)
             in
          match uu____18554 with
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
            | FStar_Extraction_ML_Syntax.MLTY_Fun (t0,uu____19181,t1) ->
                let x = FStar_Extraction_ML_Syntax.gensym ()  in
                let uu____19185 =
                  let uu____19200 =
                    let uu____19213 =
                      FStar_All.pipe_left
                        (FStar_Extraction_ML_Syntax.with_ty t0)
                        (FStar_Extraction_ML_Syntax.MLE_Var x)
                       in
                    ((x, t0), uu____19213)  in
                  uu____19200 :: more_args  in
                eta_args uu____19185 t1
            | FStar_Extraction_ML_Syntax.MLTY_Named (uu____19244,uu____19245)
                -> ((FStar_List.rev more_args), t)
            | uu____19276 ->
                let uu____19277 =
                  let uu____19279 =
                    FStar_Extraction_ML_Code.string_of_mlexpr
                      g.FStar_Extraction_ML_UEnv.currentModule mlAppExpr
                     in
                  let uu____19281 =
                    FStar_Extraction_ML_Code.string_of_mlty
                      g.FStar_Extraction_ML_UEnv.currentModule t
                     in
                  FStar_Util.format2
                    "Impossible: Head type is not an arrow: (%s : %s)"
                    uu____19279 uu____19281
                   in
                failwith uu____19277
             in
          let as_record qual1 e =
            match ((e.FStar_Extraction_ML_Syntax.expr), qual1) with
            | (FStar_Extraction_ML_Syntax.MLE_CTor
               (uu____19331,args),FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Record_ctor (tyname,fields))) ->
                let path =
                  FStar_List.map FStar_Ident.text_of_id tyname.FStar_Ident.ns
                   in
                let fields1 = record_fields fields args  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     e.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_Record (path, fields1))
            | uu____19400 -> e  in
          let resugar_and_maybe_eta qual1 e =
            let uu____19431 = eta_args [] residualType  in
            match uu____19431 with
            | (eargs,tres) ->
                (match eargs with
                 | [] ->
                     let uu____19510 = as_record qual1 e  in
                     FStar_Extraction_ML_Util.resugar_exp uu____19510
                 | uu____19517 ->
                     let uu____19532 = FStar_List.unzip eargs  in
                     (match uu____19532 with
                      | (binders,eargs1) ->
                          (match e.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_CTor (head1,args)
                               ->
                               let body =
                                 let uu____19608 =
                                   let uu____19615 =
                                     FStar_All.pipe_left
                                       (FStar_Extraction_ML_Syntax.with_ty
                                          tres)
                                       (FStar_Extraction_ML_Syntax.MLE_CTor
                                          (head1,
                                            (FStar_List.append args eargs1)))
                                      in
                                   FStar_All.pipe_left (as_record qual1)
                                     uu____19615
                                    in
                                 FStar_All.pipe_left
                                   FStar_Extraction_ML_Util.resugar_exp
                                   uu____19608
                                  in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    e.FStar_Extraction_ML_Syntax.mlty)
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    (binders, body))
                           | uu____19658 ->
                               failwith "Impossible: Not a constructor")))
             in
          match ((mlAppExpr.FStar_Extraction_ML_Syntax.expr), qual) with
          | (uu____19668,FStar_Pervasives_Native.None ) -> mlAppExpr
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____19672;
                FStar_Extraction_ML_Syntax.loc = uu____19673;_},mle::args),FStar_Pervasives_Native.Some
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
                | uu____19743 ->
                    let uu____19749 =
                      let uu____19762 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj
                         in
                      (uu____19762, args)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____19749
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
                     FStar_Extraction_ML_Syntax.mlty = uu____19781;
                     FStar_Extraction_ML_Syntax.loc = uu____19782;_},uu____19783);
                FStar_Extraction_ML_Syntax.mlty = uu____19784;
                FStar_Extraction_ML_Syntax.loc = uu____19785;_},mle::args),FStar_Pervasives_Native.Some
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
                | uu____19862 ->
                    let uu____19868 =
                      let uu____19881 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj
                         in
                      (uu____19881, args)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____19868
                 in
              FStar_Extraction_ML_Syntax.with_ty
                mlAppExpr.FStar_Extraction_ML_Syntax.mlty e
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____19900;
                FStar_Extraction_ML_Syntax.loc = uu____19901;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____19918 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____19918
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____19940;
                FStar_Extraction_ML_Syntax.loc = uu____19941;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____19943)) ->
              let uu____19971 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____19971
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____19993;
                     FStar_Extraction_ML_Syntax.loc = uu____19994;_},uu____19995);
                FStar_Extraction_ML_Syntax.mlty = uu____19996;
                FStar_Extraction_ML_Syntax.loc = uu____19997;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____20021 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____20021
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____20043;
                     FStar_Extraction_ML_Syntax.loc = uu____20044;_},uu____20045);
                FStar_Extraction_ML_Syntax.mlty = uu____20046;
                FStar_Extraction_ML_Syntax.loc = uu____20047;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____20049)) ->
              let uu____20084 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____20084
          | (FStar_Extraction_ML_Syntax.MLE_Name
             mlp,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor
             )) ->
              let uu____20108 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____20108
          | (FStar_Extraction_ML_Syntax.MLE_Name
             mlp,FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____20133)) ->
              let uu____20148 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____20148
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____20173;
                FStar_Extraction_ML_Syntax.loc = uu____20174;_},uu____20175),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____20185 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____20185
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____20210;
                FStar_Extraction_ML_Syntax.loc = uu____20211;_},uu____20212),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____20213)) ->
              let uu____20235 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____20235
          | uu____20259 -> mlAppExpr
  
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
        | uu____20308 -> (ml_e, tag)
  
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
      let maybe_generalize uu____20513 =
        match uu____20513 with
        | { FStar_Syntax_Syntax.lbname = lbname_;
            FStar_Syntax_Syntax.lbunivs = uu____20549;
            FStar_Syntax_Syntax.lbtyp = lbtyp;
            FStar_Syntax_Syntax.lbeff = lbeff;
            FStar_Syntax_Syntax.lbdef = lbdef;
            FStar_Syntax_Syntax.lbattrs = uu____20553;
            FStar_Syntax_Syntax.lbpos = uu____20554;_} ->
            let f_e = effect_as_etag g lbeff  in
            let lbtyp1 = FStar_Syntax_Subst.compress lbtyp  in
            let no_gen uu____20698 =
              let expected_t = term_as_mlty g lbtyp1  in
              (lbname_, f_e, (lbtyp1, ([], ([], expected_t))), false, lbdef)
               in
            let uu____20815 =
              FStar_TypeChecker_Util.must_erase_for_extraction
                g.FStar_Extraction_ML_UEnv.env_tcenv lbtyp1
               in
            if uu____20815
            then
              (lbname_, f_e,
                (lbtyp1, ([], ([], FStar_Extraction_ML_Syntax.MLTY_Erased))),
                false, lbdef)
            else
              (match lbtyp1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                   let uu____20952 = FStar_List.hd bs  in
                   FStar_All.pipe_right uu____20952 (is_type_binder g) ->
                   let uu____20989 = FStar_Syntax_Subst.open_comp bs c  in
                   (match uu____20989 with
                    | (bs1,c1) ->
                        let uu____21035 =
                          let uu____21057 =
                            FStar_Util.prefix_until
                              (fun x  ->
                                 let uu____21128 = is_type_binder g x  in
                                 Prims.op_Negation uu____21128) bs1
                             in
                          match uu____21057 with
                          | FStar_Pervasives_Native.None  ->
                              (bs1, (FStar_Syntax_Util.comp_result c1))
                          | FStar_Pervasives_Native.Some (bs2,b,rest) ->
                              let uu____21333 =
                                FStar_Syntax_Util.arrow (b :: rest) c1  in
                              (bs2, uu____21333)
                           in
                        (match uu____21035 with
                         | (tbinders,tbody) ->
                             let n_tbinders = FStar_List.length tbinders  in
                             let lbdef1 =
                               let uu____21456 = normalize_abs lbdef  in
                               FStar_All.pipe_right uu____21456
                                 FStar_Syntax_Util.unmeta
                                in
                             (match lbdef1.FStar_Syntax_Syntax.n with
                              | FStar_Syntax_Syntax.Tm_abs (bs2,body,copt) ->
                                  let uu____21561 =
                                    FStar_Syntax_Subst.open_term bs2 body  in
                                  (match uu____21561 with
                                   | (bs3,body1) ->
                                       if
                                         n_tbinders <=
                                           (FStar_List.length bs3)
                                       then
                                         let uu____21646 =
                                           FStar_Util.first_N n_tbinders bs3
                                            in
                                         (match uu____21646 with
                                          | (targs,rest_args) ->
                                              let expected_source_ty =
                                                let s =
                                                  FStar_List.map2
                                                    (fun uu____21810  ->
                                                       fun uu____21811  ->
                                                         match (uu____21810,
                                                                 uu____21811)
                                                         with
                                                         | ((x,uu____21857),
                                                            (y,uu____21859))
                                                             ->
                                                             let uu____21910
                                                               =
                                                               let uu____21926
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   y
                                                                  in
                                                               (x,
                                                                 uu____21926)
                                                                in
                                                             FStar_Syntax_Syntax.NT
                                                               uu____21910)
                                                    tbinders targs
                                                   in
                                                FStar_Syntax_Subst.subst s
                                                  tbody
                                                 in
                                              let env =
                                                FStar_List.fold_left
                                                  (fun env  ->
                                                     fun uu____22142  ->
                                                       match uu____22142 with
                                                       | (a,uu____22273) ->
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
                                                let uu____22294 =
                                                  FStar_All.pipe_right targs
                                                    (FStar_List.map
                                                       (fun uu____22323  ->
                                                          match uu____22323
                                                          with
                                                          | (x,uu____22337)
                                                              ->
                                                              FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                                x))
                                                   in
                                                (uu____22294, expected_t)  in
                                              let add_unit =
                                                match rest_args with
                                                | [] ->
                                                    (let uu____22368 =
                                                       is_fstar_value body1
                                                        in
                                                     Prims.op_Negation
                                                       uu____22368)
                                                      ||
                                                      (let uu____22371 =
                                                         FStar_Syntax_Util.is_pure_comp
                                                           c1
                                                          in
                                                       Prims.op_Negation
                                                         uu____22371)
                                                | uu____22373 -> false  in
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
                              | FStar_Syntax_Syntax.Tm_uinst uu____22473 ->
                                  let env =
                                    FStar_List.fold_left
                                      (fun env  ->
                                         fun uu____22678  ->
                                           match uu____22678 with
                                           | (a,uu____22809) ->
                                               FStar_Extraction_ML_UEnv.extend_ty
                                                 env a
                                                 FStar_Pervasives_Native.None)
                                      g tbinders
                                     in
                                  let expected_t = term_as_mlty env tbody  in
                                  let polytype =
                                    let uu____22830 =
                                      FStar_All.pipe_right tbinders
                                        (FStar_List.map
                                           (fun uu____22859  ->
                                              match uu____22859 with
                                              | (x,uu____22873) ->
                                                  FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                    x))
                                       in
                                    (uu____22830, expected_t)  in
                                  let args =
                                    FStar_All.pipe_right tbinders
                                      (FStar_List.map
                                         (fun uu____22945  ->
                                            match uu____22945 with
                                            | (bv,uu____22958) ->
                                                let uu____22973 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    bv
                                                   in
                                                FStar_All.pipe_right
                                                  uu____22973
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
                              | FStar_Syntax_Syntax.Tm_fvar uu____23043 ->
                                  let env =
                                    FStar_List.fold_left
                                      (fun env  ->
                                         fun uu____23241  ->
                                           match uu____23241 with
                                           | (a,uu____23372) ->
                                               FStar_Extraction_ML_UEnv.extend_ty
                                                 env a
                                                 FStar_Pervasives_Native.None)
                                      g tbinders
                                     in
                                  let expected_t = term_as_mlty env tbody  in
                                  let polytype =
                                    let uu____23393 =
                                      FStar_All.pipe_right tbinders
                                        (FStar_List.map
                                           (fun uu____23422  ->
                                              match uu____23422 with
                                              | (x,uu____23436) ->
                                                  FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                    x))
                                       in
                                    (uu____23393, expected_t)  in
                                  let args =
                                    FStar_All.pipe_right tbinders
                                      (FStar_List.map
                                         (fun uu____23508  ->
                                            match uu____23508 with
                                            | (bv,uu____23521) ->
                                                let uu____23536 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    bv
                                                   in
                                                FStar_All.pipe_right
                                                  uu____23536
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
                              | FStar_Syntax_Syntax.Tm_name uu____23606 ->
                                  let env =
                                    FStar_List.fold_left
                                      (fun env  ->
                                         fun uu____23806  ->
                                           match uu____23806 with
                                           | (a,uu____23937) ->
                                               FStar_Extraction_ML_UEnv.extend_ty
                                                 env a
                                                 FStar_Pervasives_Native.None)
                                      g tbinders
                                     in
                                  let expected_t = term_as_mlty env tbody  in
                                  let polytype =
                                    let uu____23958 =
                                      FStar_All.pipe_right tbinders
                                        (FStar_List.map
                                           (fun uu____23987  ->
                                              match uu____23987 with
                                              | (x,uu____24001) ->
                                                  FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                    x))
                                       in
                                    (uu____23958, expected_t)  in
                                  let args =
                                    FStar_All.pipe_right tbinders
                                      (FStar_List.map
                                         (fun uu____24073  ->
                                            match uu____24073 with
                                            | (bv,uu____24086) ->
                                                let uu____24101 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    bv
                                                   in
                                                FStar_All.pipe_right
                                                  uu____24101
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
                              | uu____24171 -> err_value_restriction lbdef1)))
               | uu____24199 -> no_gen ())
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
           fun uu____24741  ->
             match uu____24741 with
             | (lbname,e_tag,(typ,(binders,mltyscheme)),add_unit,_body) ->
                 let uu____24979 =
                   FStar_Extraction_ML_UEnv.extend_lb env lbname typ
                     mltyscheme add_unit is_rec
                    in
                 (match uu____24979 with
                  | (env1,uu____25125,exp_binding) ->
                      let uu____25255 =
                        let uu____25267 = FStar_Util.right lbname  in
                        (uu____25267, exp_binding)  in
                      (env1, uu____25255))) g lbs1
  
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
            (fun uu____25684  ->
               let uu____25685 = FStar_Syntax_Print.term_to_string e  in
               let uu____25687 =
                 FStar_Extraction_ML_Code.string_of_mlty
                   g.FStar_Extraction_ML_UEnv.currentModule ty
                  in
               FStar_Util.print2 "Checking %s at type %s\n" uu____25685
                 uu____25687);
          (match (f, ty) with
           | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____25697) ->
               (FStar_Extraction_ML_Syntax.ml_unit,
                 FStar_Extraction_ML_Syntax.MLTY_Erased)
           | (FStar_Extraction_ML_Syntax.E_PURE
              ,FStar_Extraction_ML_Syntax.MLTY_Erased ) ->
               (FStar_Extraction_ML_Syntax.ml_unit,
                 FStar_Extraction_ML_Syntax.MLTY_Erased)
           | uu____25704 ->
               let uu____25709 = term_as_mlexpr g e  in
               (match uu____25709 with
                | (ml_e,tag,t) ->
                    let uu____25735 = maybe_promote_effect ml_e tag t  in
                    (match uu____25735 with
                     | (ml_e1,tag1) ->
                         let uu____25758 =
                           FStar_Extraction_ML_Util.eff_leq tag1 f  in
                         if uu____25758
                         then
                           let uu____25768 =
                             maybe_coerce e.FStar_Syntax_Syntax.pos g ml_e1 t
                               ty
                              in
                           (uu____25768, ty)
                         else
                           (match (tag1, f, ty) with
                            | (FStar_Extraction_ML_Syntax.E_GHOST
                               ,FStar_Extraction_ML_Syntax.E_PURE
                               ,FStar_Extraction_ML_Syntax.MLTY_Erased ) ->
                                let uu____25787 =
                                  maybe_coerce e.FStar_Syntax_Syntax.pos g
                                    ml_e1 t ty
                                   in
                                (uu____25787, ty)
                            | uu____25797 ->
                                (err_unexpected_eff g e ty f tag1;
                                 (let uu____25805 =
                                    maybe_coerce e.FStar_Syntax_Syntax.pos g
                                      ml_e1 t ty
                                     in
                                  (uu____25805, ty)))))))

and (term_as_mlexpr :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag *
        FStar_Extraction_ML_Syntax.mlty))
  =
  fun g  ->
    fun e  ->
      let uu____25880 = term_as_mlexpr' g e  in
      match uu____25880 with
      | (e1,f,t) ->
          let uu____25908 = maybe_promote_effect e1 f t  in
          (match uu____25908 with | (e2,f1) -> (e2, f1, t))

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
           let uu____26014 =
             let uu____26016 =
               FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos  in
             let uu____26018 = FStar_Syntax_Print.tag_of_term top  in
             let uu____26020 = FStar_Syntax_Print.term_to_string top  in
             FStar_Util.format3 "%s: term_as_mlexpr' (%s) :  %s \n"
               uu____26016 uu____26018 uu____26020
              in
           FStar_Util.print_string uu____26014);
      (let t = FStar_Syntax_Subst.compress top  in
       match t.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____26041 =
             let uu____26043 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____26043
              in
           failwith uu____26041
       | FStar_Syntax_Syntax.Tm_delayed uu____26055 ->
           let uu____26086 =
             let uu____26088 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____26088
              in
           failwith uu____26086
       | FStar_Syntax_Syntax.Tm_uvar uu____26100 ->
           let uu____26121 =
             let uu____26123 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____26123
              in
           failwith uu____26121
       | FStar_Syntax_Syntax.Tm_bvar uu____26135 ->
           let uu____26141 =
             let uu____26143 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____26143
              in
           failwith uu____26141
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____26160 = FStar_Syntax_Util.unfold_lazy i  in
           term_as_mlexpr g uu____26160
       | FStar_Syntax_Syntax.Tm_type uu____26169 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_refine uu____26173 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_arrow uu____26192 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_quoted
           (qt,{
                 FStar_Syntax_Syntax.qkind =
                   FStar_Syntax_Syntax.Quote_dynamic ;
                 FStar_Syntax_Syntax.antiquotes = uu____26220;_})
           ->
           let uu____26252 =
             let uu____26261 =
               FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.failwith_lid
                 FStar_Syntax_Syntax.delta_constant
                 FStar_Pervasives_Native.None
                in
             FStar_Extraction_ML_UEnv.lookup_fv g uu____26261  in
           (match uu____26252 with
            | { FStar_Extraction_ML_UEnv.exp_b_name = uu____26277;
                FStar_Extraction_ML_UEnv.exp_b_expr = fw;
                FStar_Extraction_ML_UEnv.exp_b_tscheme = uu____26279;
                FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____26280;_} ->
                let uu____26286 =
                  let uu____26293 =
                    let uu____26294 =
                      let uu____26307 =
                        let uu____26313 =
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty
                               FStar_Extraction_ML_Syntax.ml_string_ty)
                            (FStar_Extraction_ML_Syntax.MLE_Const
                               (FStar_Extraction_ML_Syntax.MLC_String
                                  "Cannot evaluate open quotation at runtime"))
                           in
                        [uu____26313]  in
                      (fw, uu____26307)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____26294  in
                  FStar_All.pipe_left
                    (FStar_Extraction_ML_Syntax.with_ty
                       FStar_Extraction_ML_Syntax.ml_int_ty) uu____26293
                   in
                (uu____26286, FStar_Extraction_ML_Syntax.E_PURE,
                  FStar_Extraction_ML_Syntax.ml_int_ty))
       | FStar_Syntax_Syntax.Tm_quoted
           (qt,{
                 FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static ;
                 FStar_Syntax_Syntax.antiquotes = aqs;_})
           ->
           let uu____26377 = FStar_Reflection_Basic.inspect_ln qt  in
           (match uu____26377 with
            | FStar_Reflection_Data.Tv_Var bv ->
                let uu____26393 = FStar_Syntax_Syntax.lookup_aq bv aqs  in
                (match uu____26393 with
                 | FStar_Pervasives_Native.Some tm -> term_as_mlexpr g tm
                 | FStar_Pervasives_Native.None  ->
                     let tv =
                       let uu____26431 =
                         let uu____26438 =
                           FStar_Reflection_Embeddings.e_term_view_aq aqs  in
                         FStar_Syntax_Embeddings.embed uu____26438
                           (FStar_Reflection_Data.Tv_Var bv)
                          in
                       uu____26431 t.FStar_Syntax_Syntax.pos
                         FStar_Pervasives_Native.None
                         FStar_Syntax_Embeddings.id_norm_cb
                        in
                     let t1 =
                       let uu____26458 =
                         let uu____26473 = FStar_Syntax_Syntax.as_arg tv  in
                         [uu____26473]  in
                       FStar_Syntax_Util.mk_app
                         (FStar_Reflection_Data.refl_constant_term
                            FStar_Reflection_Data.fstar_refl_pack_ln)
                         uu____26458
                        in
                     term_as_mlexpr g t1)
            | tv ->
                let tv1 =
                  let uu____26520 =
                    let uu____26527 =
                      FStar_Reflection_Embeddings.e_term_view_aq aqs  in
                    FStar_Syntax_Embeddings.embed uu____26527 tv  in
                  uu____26520 t.FStar_Syntax_Syntax.pos
                    FStar_Pervasives_Native.None
                    FStar_Syntax_Embeddings.id_norm_cb
                   in
                let t1 =
                  let uu____26547 =
                    let uu____26562 = FStar_Syntax_Syntax.as_arg tv1  in
                    [uu____26562]  in
                  FStar_Syntax_Util.mk_app
                    (FStar_Reflection_Data.refl_constant_term
                       FStar_Reflection_Data.fstar_refl_pack_ln) uu____26547
                   in
                term_as_mlexpr g t1)
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_monadic (m,uu____26601)) ->
           let t2 = FStar_Syntax_Subst.compress t1  in
           (match t2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) when
                FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname ->
                let uu____26720 =
                  let uu____26747 =
                    FStar_TypeChecker_Env.effect_decl_opt
                      g.FStar_Extraction_ML_UEnv.env_tcenv m
                     in
                  FStar_Util.must uu____26747  in
                (match uu____26720 with
                 | (ed,qualifiers) ->
                     let uu____26857 =
                       let uu____26859 =
                         FStar_TypeChecker_Env.is_reifiable_effect
                           g.FStar_Extraction_ML_UEnv.env_tcenv
                           ed.FStar_Syntax_Syntax.mname
                          in
                       Prims.op_Negation uu____26859  in
                     if uu____26857
                     then term_as_mlexpr g t2
                     else
                       failwith
                         "This should not happen (should have been handled at Tm_abs level)")
            | uu____26883 -> term_as_mlexpr g t2)
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____26885) -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____26899) -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____26913 =
             FStar_TypeChecker_TcTerm.type_of_tot_term
               g.FStar_Extraction_ML_UEnv.env_tcenv t
              in
           (match uu____26913 with
            | (uu____26941,ty,uu____26943) ->
                let ml_ty = term_as_mlty g ty  in
                let uu____26969 =
                  let uu____26976 =
                    FStar_Extraction_ML_Util.mlexpr_of_const
                      t.FStar_Syntax_Syntax.pos c
                     in
                  FStar_Extraction_ML_Syntax.with_ty ml_ty uu____26976  in
                (uu____26969, FStar_Extraction_ML_Syntax.E_PURE, ml_ty))
       | FStar_Syntax_Syntax.Tm_name uu____26980 ->
           let uu____26986 = is_type g t  in
           if uu____26986
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____27003 = FStar_Extraction_ML_UEnv.lookup_term g t  in
              match uu____27003 with
              | (FStar_Util.Inl uu____27019,uu____27020) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | (FStar_Util.Inr
                 { FStar_Extraction_ML_UEnv.exp_b_name = uu____27036;
                   FStar_Extraction_ML_UEnv.exp_b_expr = x;
                   FStar_Extraction_ML_UEnv.exp_b_tscheme = mltys;
                   FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____27039;_},qual)
                  ->
                  (match mltys with
                   | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                       ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | ([],t1) ->
                       let uu____27072 =
                         maybe_eta_data_and_project_record g qual t1 x  in
                       (uu____27072, FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | uu____27082 -> instantiate_maybe_partial x mltys []))
       | FStar_Syntax_Syntax.Tm_fvar fv ->
           let uu____27087 = is_type g t  in
           if uu____27087
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____27104 = FStar_Extraction_ML_UEnv.try_lookup_fv g fv
                 in
              match uu____27104 with
              | FStar_Pervasives_Native.None  ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.MLTY_Erased)
              | FStar_Pervasives_Native.Some
                  { FStar_Extraction_ML_UEnv.exp_b_name = uu____27127;
                    FStar_Extraction_ML_UEnv.exp_b_expr = x;
                    FStar_Extraction_ML_UEnv.exp_b_tscheme = mltys;
                    FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____27130;_}
                  ->
                  (FStar_Extraction_ML_UEnv.debug g
                     (fun uu____27145  ->
                        let uu____27146 = FStar_Syntax_Print.fv_to_string fv
                           in
                        let uu____27148 =
                          FStar_Extraction_ML_Code.string_of_mlexpr
                            g.FStar_Extraction_ML_UEnv.currentModule x
                           in
                        let uu____27150 =
                          FStar_Extraction_ML_Code.string_of_mlty
                            g.FStar_Extraction_ML_UEnv.currentModule
                            (FStar_Pervasives_Native.snd mltys)
                           in
                        FStar_Util.print3 "looked up %s: got %s at %s \n"
                          uu____27146 uu____27148 uu____27150);
                   (match mltys with
                    | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                        ->
                        (FStar_Extraction_ML_Syntax.ml_unit,
                          FStar_Extraction_ML_Syntax.E_PURE, t1)
                    | ([],t1) ->
                        let uu____27169 =
                          maybe_eta_data_and_project_record g
                            fv.FStar_Syntax_Syntax.fv_qual t1 x
                           in
                        (uu____27169, FStar_Extraction_ML_Syntax.E_PURE, t1)
                    | uu____27179 -> instantiate_maybe_partial x mltys [])))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,rcopt) ->
           let uu____27239 = FStar_Syntax_Subst.open_term bs body  in
           (match uu____27239 with
            | (bs1,body1) ->
                let uu____27267 = binders_as_ml_binders g bs1  in
                (match uu____27267 with
                 | (ml_bs,env) ->
                     let body2 =
                       match rcopt with
                       | FStar_Pervasives_Native.Some rc ->
                           let uu____27509 =
                             FStar_TypeChecker_Env.is_reifiable_rc
                               env.FStar_Extraction_ML_UEnv.env_tcenv rc
                              in
                           if uu____27509
                           then
                             FStar_TypeChecker_Util.reify_body
                               env.FStar_Extraction_ML_UEnv.env_tcenv body1
                           else body1
                       | FStar_Pervasives_Native.None  ->
                           (FStar_Extraction_ML_UEnv.debug g
                              (fun uu____27528  ->
                                 let uu____27529 =
                                   FStar_Syntax_Print.term_to_string body1
                                    in
                                 FStar_Util.print1
                                   "No computation type for: %s\n"
                                   uu____27529);
                            body1)
                        in
                     let uu____27532 = term_as_mlexpr env body2  in
                     (match uu____27532 with
                      | (ml_body,f,t1) ->
                          let uu____27560 =
                            FStar_List.fold_right
                              (fun uu____27580  ->
                                 fun uu____27581  ->
                                   match (uu____27580, uu____27581) with
                                   | ((uu____27604,targ),(f1,t2)) ->
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         (FStar_Extraction_ML_Syntax.MLTY_Fun
                                            (targ, f1, t2)))) ml_bs (f, t1)
                             in
                          (match uu____27560 with
                           | (f1,tfun) ->
                               let uu____27630 =
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty tfun)
                                   (FStar_Extraction_ML_Syntax.MLE_Fun
                                      (ml_bs, ml_body))
                                  in
                               (uu____27630, f1, tfun)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____27653;
              FStar_Syntax_Syntax.vars = uu____27654;_},(a1,uu____27656)::[])
           ->
           let ty =
             let uu____27724 =
               FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid  in
             term_as_mlty g uu____27724  in
           let uu____27733 =
             let uu____27740 =
               FStar_Extraction_ML_Util.mlexpr_of_range
                 a1.FStar_Syntax_Syntax.pos
                in
             FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty)
               uu____27740
              in
           (uu____27733, FStar_Extraction_ML_Syntax.E_PURE, ty)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____27747;
              FStar_Syntax_Syntax.vars = uu____27748;_},(t1,uu____27750)::
            (r,uu____27752)::[])
           -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____27847);
              FStar_Syntax_Syntax.pos = uu____27848;
              FStar_Syntax_Syntax.vars = uu____27849;_},uu____27850)
           -> failwith "Unreachable? Tm_app Const_reflect"
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let is_total rc =
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_Tot_lid)
               ||
               (FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
                  (FStar_List.existsb
                     (fun uu___1_27972  ->
                        match uu___1_27972 with
                        | FStar_Syntax_Syntax.TOTAL  -> true
                        | uu____27975 -> false)))
              in
           let uu____27977 =
             let uu____27982 =
               let uu____27983 = FStar_Syntax_Subst.compress head1  in
               uu____27983.FStar_Syntax_Syntax.n  in
             ((head1.FStar_Syntax_Syntax.n), uu____27982)  in
           (match uu____27977 with
            | (FStar_Syntax_Syntax.Tm_uvar uu____28003,uu____28004) ->
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
            | (uu____28034,FStar_Syntax_Syntax.Tm_abs
               (bs,uu____28036,FStar_Pervasives_Native.Some rc)) when
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
            | (uu____28108,FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_reify )) ->
                let e =
                  let uu____28118 = FStar_List.hd args  in
                  FStar_TypeChecker_Util.reify_body_with_arg
                    g.FStar_Extraction_ML_UEnv.env_tcenv head1 uu____28118
                   in
                let tm =
                  let uu____28142 =
                    let uu____28147 = FStar_TypeChecker_Util.remove_reify e
                       in
                    let uu____28156 = FStar_List.tl args  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____28147 uu____28156  in
                  uu____28142 FStar_Pervasives_Native.None
                    t.FStar_Syntax_Syntax.pos
                   in
                term_as_mlexpr g tm
            | uu____28169 ->
                let rec extract_app is_data uu____28235 uu____28236 restArgs
                  =
                  match (uu____28235, uu____28236) with
                  | ((mlhead,mlargs_f),(f,t1)) ->
                      let mk_head uu____28357 =
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
                         (fun uu____28414  ->
                            let uu____28415 =
                              let uu____28417 = mk_head ()  in
                              FStar_Extraction_ML_Code.string_of_mlexpr
                                g.FStar_Extraction_ML_UEnv.currentModule
                                uu____28417
                               in
                            let uu____28424 =
                              FStar_Extraction_ML_Code.string_of_mlty
                                g.FStar_Extraction_ML_UEnv.currentModule t1
                               in
                            let uu____28426 =
                              match restArgs with
                              | [] -> "none"
                              | (hd1,uu____28441)::uu____28442 ->
                                  FStar_Syntax_Print.term_to_string hd1
                               in
                            FStar_Util.print3
                              "extract_app ml_head=%s type of head = %s, next arg = %s\n"
                              uu____28415 uu____28424 uu____28426);
                       (match (restArgs, t1) with
                        | ([],uu____28499) ->
                            let app =
                              let uu____28529 = mk_head ()  in
                              maybe_eta_data_and_project_record g is_data t1
                                uu____28529
                               in
                            (app, f, t1)
                        | ((arg,uu____28540)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                           (formal_t,f',t2)) when
                            (is_type g arg) &&
                              (type_leq g formal_t
                                 FStar_Extraction_ML_Syntax.ml_unit_ty)
                            ->
                            let uu____28591 =
                              let uu____28596 =
                                FStar_Extraction_ML_Util.join
                                  arg.FStar_Syntax_Syntax.pos f f'
                                 in
                              (uu____28596, t2)  in
                            extract_app is_data
                              (mlhead,
                                ((FStar_Extraction_ML_Syntax.ml_unit,
                                   FStar_Extraction_ML_Syntax.E_PURE) ::
                                mlargs_f)) uu____28591 rest
                        | ((e0,uu____28620)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                           (tExpected,f',t2)) ->
                            let r = e0.FStar_Syntax_Syntax.pos  in
                            let expected_effect =
                              let uu____28673 =
                                (FStar_Options.lax ()) &&
                                  (FStar_TypeChecker_Util.short_circuit_head
                                     head1)
                                 in
                              if uu____28673
                              then FStar_Extraction_ML_Syntax.E_IMPURE
                              else FStar_Extraction_ML_Syntax.E_PURE  in
                            let uu____28678 =
                              check_term_as_mlexpr g e0 expected_effect
                                tExpected
                               in
                            (match uu____28678 with
                             | (e01,tInferred) ->
                                 let uu____28703 =
                                   let uu____28708 =
                                     FStar_Extraction_ML_Util.join_l r
                                       [f; f']
                                      in
                                   (uu____28708, t2)  in
                                 extract_app is_data
                                   (mlhead, ((e01, expected_effect) ::
                                     mlargs_f)) uu____28703 rest)
                        | uu____28731 ->
                            let uu____28748 =
                              FStar_Extraction_ML_Util.udelta_unfold g t1  in
                            (match uu____28748 with
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
                                  | uu____28894 ->
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
                let extract_app_maybe_projector is_data mlhead uu____29020
                  args1 =
                  match uu____29020 with
                  | (f,t1) ->
                      (match is_data with
                       | FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_projector uu____29063)
                           ->
                           let rec remove_implicits args2 f1 t2 =
                             match (args2, t2) with
                             | ((a0,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____29173))::args3,FStar_Extraction_ML_Syntax.MLTY_Fun
                                (uu____29175,f',t3)) ->
                                 let uu____29233 =
                                   FStar_Extraction_ML_Util.join
                                     a0.FStar_Syntax_Syntax.pos f1 f'
                                    in
                                 remove_implicits args3 uu____29233 t3
                             | uu____29234 -> (args2, f1, t2)  in
                           let uu____29267 = remove_implicits args1 f t1  in
                           (match uu____29267 with
                            | (args2,f1,t2) ->
                                extract_app is_data (mlhead, []) (f1, t2)
                                  args2)
                       | uu____29347 ->
                           extract_app is_data (mlhead, []) (f, t1) args1)
                   in
                let extract_app_with_instantiations uu____29383 =
                  let head2 = FStar_Syntax_Util.un_uinst head1  in
                  match head2.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_name uu____29402 ->
                      let uu____29408 =
                        let uu____29432 =
                          FStar_Extraction_ML_UEnv.lookup_term g head2  in
                        match uu____29432 with
                        | (FStar_Util.Inr exp_b,q) ->
                            (FStar_Extraction_ML_UEnv.debug g
                               (fun uu____29484  ->
                                  let uu____29485 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  let uu____29487 =
                                    FStar_Extraction_ML_Code.string_of_mlexpr
                                      g.FStar_Extraction_ML_UEnv.currentModule
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_expr
                                     in
                                  let uu____29489 =
                                    FStar_Extraction_ML_Code.string_of_mlty
                                      g.FStar_Extraction_ML_UEnv.currentModule
                                      (FStar_Pervasives_Native.snd
                                         exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme)
                                     in
                                  let uu____29491 =
                                    FStar_Util.string_of_bool
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok
                                     in
                                  FStar_Util.print4
                                    "@@@looked up %s: got %s at %s (inst_ok=%s)\n"
                                    uu____29485 uu____29487 uu____29489
                                    uu____29491);
                             (((exp_b.FStar_Extraction_ML_UEnv.exp_b_expr),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok)),
                               q))
                        | uu____29524 -> failwith "FIXME Ty"  in
                      (match uu____29408 with
                       | ((head_ml,(vars,t1),inst_ok),qual) ->
                           let has_typ_apps =
                             match args with
                             | (a,uu____29615)::uu____29616 -> is_type g a
                             | uu____29659 -> false  in
                           let uu____29675 =
                             match vars with
                             | uu____29718::uu____29719 when
                                 (Prims.op_Negation has_typ_apps) && inst_ok
                                 -> (head_ml, t1, args)
                             | uu____29740 ->
                                 let n1 = FStar_List.length vars  in
                                 let uu____29746 =
                                   if (FStar_List.length args) <= n1
                                   then
                                     let uu____29796 =
                                       FStar_List.map
                                         (fun uu____29812  ->
                                            match uu____29812 with
                                            | (x,uu____29824) ->
                                                term_as_mlty g x) args
                                        in
                                     (uu____29796, [])
                                   else
                                     (let uu____29863 =
                                        FStar_Util.first_N n1 args  in
                                      match uu____29863 with
                                      | (prefix1,rest) ->
                                          let uu____29984 =
                                            FStar_List.map
                                              (fun uu____30000  ->
                                                 match uu____30000 with
                                                 | (x,uu____30012) ->
                                                     term_as_mlty g x)
                                              prefix1
                                             in
                                          (uu____29984, rest))
                                    in
                                 (match uu____29746 with
                                  | (provided_type_args,rest) ->
                                      let uu____30090 =
                                        match head_ml.FStar_Extraction_ML_Syntax.expr
                                        with
                                        | FStar_Extraction_ML_Syntax.MLE_Name
                                            uu____30105 ->
                                            let uu____30106 =
                                              instantiate_maybe_partial
                                                head_ml (vars, t1)
                                                provided_type_args
                                               in
                                            (match uu____30106 with
                                             | (head3,uu____30124,t2) ->
                                                 (head3, t2))
                                        | FStar_Extraction_ML_Syntax.MLE_Var
                                            uu____30135 ->
                                            let uu____30137 =
                                              instantiate_maybe_partial
                                                head_ml (vars, t1)
                                                provided_type_args
                                               in
                                            (match uu____30137 with
                                             | (head3,uu____30155,t2) ->
                                                 (head3, t2))
                                        | FStar_Extraction_ML_Syntax.MLE_App
                                            (head3,{
                                                     FStar_Extraction_ML_Syntax.expr
                                                       =
                                                       FStar_Extraction_ML_Syntax.MLE_Const
                                                       (FStar_Extraction_ML_Syntax.MLC_Unit
                                                       );
                                                     FStar_Extraction_ML_Syntax.mlty
                                                       = uu____30167;
                                                     FStar_Extraction_ML_Syntax.loc
                                                       = uu____30168;_}::[])
                                            ->
                                            let uu____30186 =
                                              instantiate_maybe_partial head3
                                                (vars, t1) provided_type_args
                                               in
                                            (match uu____30186 with
                                             | (head4,uu____30204,t2) ->
                                                 let uu____30212 =
                                                   FStar_All.pipe_right
                                                     (FStar_Extraction_ML_Syntax.MLE_App
                                                        (head4,
                                                          [FStar_Extraction_ML_Syntax.ml_unit]))
                                                     (FStar_Extraction_ML_Syntax.with_ty
                                                        t2)
                                                    in
                                                 (uu____30212, t2))
                                        | uu____30239 ->
                                            failwith
                                              "Impossible: Unexpected head term"
                                         in
                                      (match uu____30090 with
                                       | (head3,t2) -> (head3, t2, rest)))
                              in
                           (match uu____29675 with
                            | (head_ml1,head_t,args1) ->
                                (match args1 with
                                 | [] ->
                                     let uu____30353 =
                                       maybe_eta_data_and_project_record g
                                         qual head_t head_ml1
                                        in
                                     (uu____30353,
                                       FStar_Extraction_ML_Syntax.E_PURE,
                                       head_t)
                                 | uu____30363 ->
                                     extract_app_maybe_projector qual
                                       head_ml1
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         head_t) args1)))
                  | FStar_Syntax_Syntax.Tm_fvar uu____30376 ->
                      let uu____30380 =
                        let uu____30404 =
                          FStar_Extraction_ML_UEnv.lookup_term g head2  in
                        match uu____30404 with
                        | (FStar_Util.Inr exp_b,q) ->
                            (FStar_Extraction_ML_UEnv.debug g
                               (fun uu____30456  ->
                                  let uu____30457 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  let uu____30459 =
                                    FStar_Extraction_ML_Code.string_of_mlexpr
                                      g.FStar_Extraction_ML_UEnv.currentModule
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_expr
                                     in
                                  let uu____30461 =
                                    FStar_Extraction_ML_Code.string_of_mlty
                                      g.FStar_Extraction_ML_UEnv.currentModule
                                      (FStar_Pervasives_Native.snd
                                         exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme)
                                     in
                                  let uu____30463 =
                                    FStar_Util.string_of_bool
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok
                                     in
                                  FStar_Util.print4
                                    "@@@looked up %s: got %s at %s (inst_ok=%s)\n"
                                    uu____30457 uu____30459 uu____30461
                                    uu____30463);
                             (((exp_b.FStar_Extraction_ML_UEnv.exp_b_expr),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok)),
                               q))
                        | uu____30496 -> failwith "FIXME Ty"  in
                      (match uu____30380 with
                       | ((head_ml,(vars,t1),inst_ok),qual) ->
                           let has_typ_apps =
                             match args with
                             | (a,uu____30587)::uu____30588 -> is_type g a
                             | uu____30631 -> false  in
                           let uu____30647 =
                             match vars with
                             | uu____30690::uu____30691 when
                                 (Prims.op_Negation has_typ_apps) && inst_ok
                                 -> (head_ml, t1, args)
                             | uu____30712 ->
                                 let n1 = FStar_List.length vars  in
                                 let uu____30718 =
                                   if (FStar_List.length args) <= n1
                                   then
                                     let uu____30768 =
                                       FStar_List.map
                                         (fun uu____30784  ->
                                            match uu____30784 with
                                            | (x,uu____30796) ->
                                                term_as_mlty g x) args
                                        in
                                     (uu____30768, [])
                                   else
                                     (let uu____30835 =
                                        FStar_Util.first_N n1 args  in
                                      match uu____30835 with
                                      | (prefix1,rest) ->
                                          let uu____30956 =
                                            FStar_List.map
                                              (fun uu____30972  ->
                                                 match uu____30972 with
                                                 | (x,uu____30984) ->
                                                     term_as_mlty g x)
                                              prefix1
                                             in
                                          (uu____30956, rest))
                                    in
                                 (match uu____30718 with
                                  | (provided_type_args,rest) ->
                                      let uu____31062 =
                                        match head_ml.FStar_Extraction_ML_Syntax.expr
                                        with
                                        | FStar_Extraction_ML_Syntax.MLE_Name
                                            uu____31077 ->
                                            let uu____31078 =
                                              instantiate_maybe_partial
                                                head_ml (vars, t1)
                                                provided_type_args
                                               in
                                            (match uu____31078 with
                                             | (head3,uu____31096,t2) ->
                                                 (head3, t2))
                                        | FStar_Extraction_ML_Syntax.MLE_Var
                                            uu____31107 ->
                                            let uu____31109 =
                                              instantiate_maybe_partial
                                                head_ml (vars, t1)
                                                provided_type_args
                                               in
                                            (match uu____31109 with
                                             | (head3,uu____31127,t2) ->
                                                 (head3, t2))
                                        | FStar_Extraction_ML_Syntax.MLE_App
                                            (head3,{
                                                     FStar_Extraction_ML_Syntax.expr
                                                       =
                                                       FStar_Extraction_ML_Syntax.MLE_Const
                                                       (FStar_Extraction_ML_Syntax.MLC_Unit
                                                       );
                                                     FStar_Extraction_ML_Syntax.mlty
                                                       = uu____31139;
                                                     FStar_Extraction_ML_Syntax.loc
                                                       = uu____31140;_}::[])
                                            ->
                                            let uu____31158 =
                                              instantiate_maybe_partial head3
                                                (vars, t1) provided_type_args
                                               in
                                            (match uu____31158 with
                                             | (head4,uu____31176,t2) ->
                                                 let uu____31184 =
                                                   FStar_All.pipe_right
                                                     (FStar_Extraction_ML_Syntax.MLE_App
                                                        (head4,
                                                          [FStar_Extraction_ML_Syntax.ml_unit]))
                                                     (FStar_Extraction_ML_Syntax.with_ty
                                                        t2)
                                                    in
                                                 (uu____31184, t2))
                                        | uu____31211 ->
                                            failwith
                                              "Impossible: Unexpected head term"
                                         in
                                      (match uu____31062 with
                                       | (head3,t2) -> (head3, t2, rest)))
                              in
                           (match uu____30647 with
                            | (head_ml1,head_t,args1) ->
                                (match args1 with
                                 | [] ->
                                     let uu____31325 =
                                       maybe_eta_data_and_project_record g
                                         qual head_t head_ml1
                                        in
                                     (uu____31325,
                                       FStar_Extraction_ML_Syntax.E_PURE,
                                       head_t)
                                 | uu____31335 ->
                                     extract_app_maybe_projector qual
                                       head_ml1
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         head_t) args1)))
                  | uu____31348 ->
                      let uu____31349 = term_as_mlexpr g head2  in
                      (match uu____31349 with
                       | (head3,f,t1) ->
                           extract_app_maybe_projector
                             FStar_Pervasives_Native.None head3 (f, t1) args)
                   in
                let uu____31377 = is_type g t  in
                if uu____31377
                then
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
                else
                  (let uu____31394 =
                     let uu____31395 = FStar_Syntax_Util.un_uinst head1  in
                     uu____31395.FStar_Syntax_Syntax.n  in
                   match uu____31394 with
                   | FStar_Syntax_Syntax.Tm_fvar fv ->
                       let uu____31419 =
                         FStar_Extraction_ML_UEnv.try_lookup_fv g fv  in
                       (match uu____31419 with
                        | FStar_Pervasives_Native.None  ->
                            (FStar_Extraction_ML_Syntax.ml_unit,
                              FStar_Extraction_ML_Syntax.E_PURE,
                              FStar_Extraction_ML_Syntax.MLTY_Erased)
                        | uu____31442 -> extract_app_with_instantiations ())
                   | uu____31449 -> extract_app_with_instantiations ()))
       | FStar_Syntax_Syntax.Tm_ascribed (e0,(tc,uu____31452),f) ->
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
           let uu____31608 = check_term_as_mlexpr g e0 f1 t1  in
           (match uu____31608 with | (e,t2) -> (e, f1, t2))
       | FStar_Syntax_Syntax.Tm_let ((is_rec,lbs),e') ->
           let top_level = FStar_Syntax_Syntax.is_top_level lbs  in
           let uu____31687 =
             if is_rec
             then FStar_Syntax_Subst.open_let_rec lbs e'
             else
               (let uu____31725 = FStar_Syntax_Syntax.is_top_level lbs  in
                if uu____31725
                then (lbs, e')
                else
                  (let lb = FStar_List.hd lbs  in
                   let x =
                     let uu____31793 =
                       FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                     FStar_Syntax_Syntax.freshen_bv uu____31793  in
                   let lb1 =
                     let uu___1710_31827 = lb  in
                     {
                       FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                       FStar_Syntax_Syntax.lbunivs =
                         (uu___1710_31827.FStar_Syntax_Syntax.lbunivs);
                       FStar_Syntax_Syntax.lbtyp =
                         (uu___1710_31827.FStar_Syntax_Syntax.lbtyp);
                       FStar_Syntax_Syntax.lbeff =
                         (uu___1710_31827.FStar_Syntax_Syntax.lbeff);
                       FStar_Syntax_Syntax.lbdef =
                         (uu___1710_31827.FStar_Syntax_Syntax.lbdef);
                       FStar_Syntax_Syntax.lbattrs =
                         (uu___1710_31827.FStar_Syntax_Syntax.lbattrs);
                       FStar_Syntax_Syntax.lbpos =
                         (uu___1710_31827.FStar_Syntax_Syntax.lbpos)
                     }  in
                   let e'1 =
                     FStar_Syntax_Subst.subst
                       [FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x)] e'
                      in
                   ([lb1], e'1)))
              in
           (match uu____31687 with
            | (lbs1,e'1) ->
                let lbs2 =
                  if top_level
                  then
                    FStar_All.pipe_right lbs1
                      (FStar_List.map
                         (fun lb  ->
                            let tcenv =
                              let uu____32103 =
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
                                uu____32103
                               in
                            let lbdef =
                              let uu____32134 = FStar_Options.ml_ish ()  in
                              if uu____32134
                              then lb.FStar_Syntax_Syntax.lbdef
                              else
                                (let norm_call uu____32154 =
                                   FStar_TypeChecker_Normalize.normalize
                                     (FStar_TypeChecker_Env.PureSubtermsWithinComputations
                                     :: extraction_norm_steps) tcenv
                                     lb.FStar_Syntax_Syntax.lbdef
                                    in
                                 let uu____32155 =
                                   (FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug tcenv)
                                      (FStar_Options.Other "Extraction"))
                                     ||
                                     (FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug tcenv)
                                        (FStar_Options.Other "ExtractNorm"))
                                    in
                                 if uu____32155
                                 then
                                   ((let uu____32169 =
                                       FStar_Syntax_Print.lbname_to_string
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     let uu____32171 =
                                       FStar_Syntax_Print.term_to_string
                                         lb.FStar_Syntax_Syntax.lbdef
                                        in
                                     FStar_Util.print2
                                       "Starting to normalize top-level let %s)\n\tlbdef=%s"
                                       uu____32169 uu____32171);
                                    (let a =
                                       let uu____32185 =
                                         let uu____32187 =
                                           FStar_Syntax_Print.lbname_to_string
                                             lb.FStar_Syntax_Syntax.lbname
                                            in
                                         FStar_Util.format1
                                           "###(Time to normalize top-level let %s)"
                                           uu____32187
                                          in
                                       FStar_Util.measure_execution_time
                                         uu____32185 norm_call
                                        in
                                     (let uu____32197 =
                                        FStar_Syntax_Print.term_to_string a
                                         in
                                      FStar_Util.print1 "Normalized to %s\n"
                                        uu____32197);
                                     a))
                                 else norm_call ())
                               in
                            let uu___1728_32202 = lb  in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___1728_32202.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___1728_32202.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp =
                                (uu___1728_32202.FStar_Syntax_Syntax.lbtyp);
                              FStar_Syntax_Syntax.lbeff =
                                (uu___1728_32202.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = lbdef;
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___1728_32202.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___1728_32202.FStar_Syntax_Syntax.lbpos)
                            }))
                  else lbs1  in
                let check_lb env uu____32347 =
                  match uu____32347 with
                  | (nm,(_lbname,f,(_t,(targs,polytype)),add_unit,e)) ->
                      let env1 =
                        FStar_List.fold_left
                          (fun env1  ->
                             fun uu____32816  ->
                               match uu____32816 with
                               | (a,uu____32947) ->
                                   FStar_Extraction_ML_UEnv.extend_ty env1 a
                                     FStar_Pervasives_Native.None) env targs
                         in
                      let expected_t = FStar_Pervasives_Native.snd polytype
                         in
                      let uu____32963 =
                        check_term_as_mlexpr env1 e f expected_t  in
                      (match uu____32963 with
                       | (e1,ty) ->
                           let uu____32989 =
                             maybe_promote_effect e1 f expected_t  in
                           (match uu____32989 with
                            | (e2,f1) ->
                                let meta =
                                  match (f1, ty) with
                                  | (FStar_Extraction_ML_Syntax.E_PURE
                                     ,FStar_Extraction_ML_Syntax.MLTY_Erased
                                     ) -> [FStar_Extraction_ML_Syntax.Erased]
                                  | (FStar_Extraction_ML_Syntax.E_GHOST
                                     ,FStar_Extraction_ML_Syntax.MLTY_Erased
                                     ) -> [FStar_Extraction_ML_Syntax.Erased]
                                  | uu____33016 -> []  in
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
                let uu____33068 =
                  FStar_List.fold_right
                    (fun lb  ->
                       fun uu____33307  ->
                         match uu____33307 with
                         | (env,lbs4) ->
                             let uu____33717 = lb  in
                             (match uu____33717 with
                              | (lbname,uu____33843,(t1,(uu____33845,polytype)),add_unit,uu____33848)
                                  ->
                                  let uu____33883 =
                                    FStar_Extraction_ML_UEnv.extend_lb env
                                      lbname t1 polytype add_unit true
                                     in
                                  (match uu____33883 with
                                   | (env1,nm,uu____34054) ->
                                       (env1, ((nm, lb) :: lbs4))))) lbs3
                    (g, [])
                   in
                (match uu____33068 with
                 | (env_body,lbs4) ->
                     let env_def = if is_rec then env_body else g  in
                     let lbs5 =
                       FStar_All.pipe_right lbs4
                         (FStar_List.map (check_lb env_def))
                        in
                     let e'_rng = e'1.FStar_Syntax_Syntax.pos  in
                     let uu____34975 = term_as_mlexpr env_body e'1  in
                     (match uu____34975 with
                      | (e'2,f',t') ->
                          let f =
                            let uu____35004 =
                              let uu____35007 =
                                FStar_List.map FStar_Pervasives_Native.fst
                                  lbs5
                                 in
                              f' :: uu____35007  in
                            FStar_Extraction_ML_Util.join_l e'_rng
                              uu____35004
                             in
                          let is_rec1 =
                            if is_rec = true
                            then FStar_Extraction_ML_Syntax.Rec
                            else FStar_Extraction_ML_Syntax.NonRec  in
                          let uu____35032 =
                            let uu____35039 =
                              let uu____35040 =
                                let uu____35041 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    lbs5
                                   in
                                (is_rec1, uu____35041)  in
                              mk_MLE_Let top_level uu____35040 e'2  in
                            let uu____35080 =
                              FStar_Extraction_ML_Util.mlloc_of_range
                                t.FStar_Syntax_Syntax.pos
                               in
                            FStar_Extraction_ML_Syntax.with_ty_loc t'
                              uu____35039 uu____35080
                             in
                          (uu____35032, f, t'))))
       | FStar_Syntax_Syntax.Tm_match (scrutinee,pats) ->
           let uu____35152 = term_as_mlexpr g scrutinee  in
           (match uu____35152 with
            | (e,f_e,t_e) ->
                let uu____35180 = check_pats_for_ite pats  in
                (match uu____35180 with
                 | (b,then_e,else_e) ->
                     let no_lift x t1 = x  in
                     if b
                     then
                       (match (then_e, else_e) with
                        | (FStar_Pervasives_Native.Some
                           then_e1,FStar_Pervasives_Native.Some else_e1) ->
                            let uu____35319 = term_as_mlexpr g then_e1  in
                            (match uu____35319 with
                             | (then_mle,f_then,t_then) ->
                                 let uu____35347 = term_as_mlexpr g else_e1
                                    in
                                 (match uu____35347 with
                                  | (else_mle,f_else,t_else) ->
                                      let uu____35375 =
                                        let uu____35392 =
                                          type_leq g t_then t_else  in
                                        if uu____35392
                                        then (t_else, no_lift)
                                        else
                                          (let uu____35425 =
                                             type_leq g t_else t_then  in
                                           if uu____35425
                                           then (t_then, no_lift)
                                           else
                                             (FStar_Extraction_ML_Syntax.MLTY_Top,
                                               FStar_Extraction_ML_Syntax.apply_obj_repr))
                                         in
                                      (match uu____35375 with
                                       | (t_branch,maybe_lift1) ->
                                           let uu____35505 =
                                             let uu____35512 =
                                               let uu____35513 =
                                                 let uu____35531 =
                                                   maybe_lift1 then_mle
                                                     t_then
                                                    in
                                                 let uu____35538 =
                                                   let uu____35544 =
                                                     maybe_lift1 else_mle
                                                       t_else
                                                      in
                                                   FStar_Pervasives_Native.Some
                                                     uu____35544
                                                    in
                                                 (e, uu____35531,
                                                   uu____35538)
                                                  in
                                               FStar_Extraction_ML_Syntax.MLE_If
                                                 uu____35513
                                                in
                                             FStar_All.pipe_left
                                               (FStar_Extraction_ML_Syntax.with_ty
                                                  t_branch) uu____35512
                                              in
                                           let uu____35568 =
                                             FStar_Extraction_ML_Util.join
                                               then_e1.FStar_Syntax_Syntax.pos
                                               f_then f_else
                                              in
                                           (uu____35505, uu____35568,
                                             t_branch))))
                        | uu____35572 ->
                            failwith
                              "ITE pats matched but then and else expressions not found?")
                     else
                       (let uu____35601 =
                          FStar_All.pipe_right pats
                            (FStar_Util.fold_map
                               (fun compat  ->
                                  fun br  ->
                                    let uu____35718 =
                                      FStar_Syntax_Subst.open_branch br  in
                                    match uu____35718 with
                                    | (pat,when_opt,branch1) ->
                                        let uu____35791 =
                                          extract_pat g pat t_e
                                            term_as_mlexpr
                                           in
                                        (match uu____35791 with
                                         | (env,p,pat_t_compat) ->
                                             let uu____36045 =
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
                                                   let uu____36092 =
                                                     term_as_mlexpr env w  in
                                                   (match uu____36092 with
                                                    | (w1,f_w,t_w) ->
                                                        let w2 =
                                                          maybe_coerce w_pos
                                                            env w1 t_w
                                                            FStar_Extraction_ML_Syntax.ml_bool_ty
                                                           in
                                                        ((FStar_Pervasives_Native.Some
                                                            w2), f_w))
                                                in
                                             (match uu____36045 with
                                              | (when_opt1,f_when) ->
                                                  let uu____36178 =
                                                    term_as_mlexpr env
                                                      branch1
                                                     in
                                                  (match uu____36178 with
                                                   | (mlbranch,f_branch,t_branch)
                                                       ->
                                                       let uu____36228 =
                                                         FStar_All.pipe_right
                                                           p
                                                           (FStar_List.map
                                                              (fun
                                                                 uu____36329 
                                                                 ->
                                                                 match uu____36329
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
                                                         uu____36228)))))
                               true)
                           in
                        match uu____35601 with
                        | (pat_t_compat,mlbranches) ->
                            let mlbranches1 = FStar_List.flatten mlbranches
                               in
                            let e1 =
                              if pat_t_compat
                              then e
                              else
                                (FStar_Extraction_ML_UEnv.debug g
                                   (fun uu____36572  ->
                                      let uu____36573 =
                                        FStar_Extraction_ML_Code.string_of_mlexpr
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          e
                                         in
                                      let uu____36575 =
                                        FStar_Extraction_ML_Code.string_of_mlty
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          t_e
                                         in
                                      FStar_Util.print2
                                        "Coercing scrutinee %s from type %s because pattern type is incompatible\n"
                                        uu____36573 uu____36575);
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty t_e)
                                   (FStar_Extraction_ML_Syntax.MLE_Coerce
                                      (e, t_e,
                                        FStar_Extraction_ML_Syntax.MLTY_Top)))
                               in
                            (match mlbranches1 with
                             | [] ->
                                 let uu____36617 =
                                   let uu____36626 =
                                     FStar_Syntax_Syntax.lid_as_fv
                                       FStar_Parser_Const.failwith_lid
                                       FStar_Syntax_Syntax.delta_constant
                                       FStar_Pervasives_Native.None
                                      in
                                   FStar_Extraction_ML_UEnv.lookup_fv g
                                     uu____36626
                                    in
                                 (match uu____36617 with
                                  | {
                                      FStar_Extraction_ML_UEnv.exp_b_name =
                                        uu____36642;
                                      FStar_Extraction_ML_UEnv.exp_b_expr =
                                        fw;
                                      FStar_Extraction_ML_UEnv.exp_b_tscheme
                                        = uu____36644;
                                      FStar_Extraction_ML_UEnv.exp_b_inst_ok
                                        = uu____36645;_}
                                      ->
                                      let uu____36651 =
                                        let uu____36658 =
                                          let uu____36659 =
                                            let uu____36672 =
                                              let uu____36678 =
                                                FStar_All.pipe_left
                                                  (FStar_Extraction_ML_Syntax.with_ty
                                                     FStar_Extraction_ML_Syntax.ml_string_ty)
                                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                                     (FStar_Extraction_ML_Syntax.MLC_String
                                                        "unreachable"))
                                                 in
                                              [uu____36678]  in
                                            (fw, uu____36672)  in
                                          FStar_Extraction_ML_Syntax.MLE_App
                                            uu____36659
                                           in
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             FStar_Extraction_ML_Syntax.ml_int_ty)
                                          uu____36658
                                         in
                                      (uu____36651,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        FStar_Extraction_ML_Syntax.ml_int_ty))
                             | (uu____36709,uu____36710,(uu____36711,f_first,t_first))::rest
                                 ->
                                 let uu____36798 =
                                   FStar_List.fold_left
                                     (fun uu____36846  ->
                                        fun uu____36847  ->
                                          match (uu____36846, uu____36847)
                                          with
                                          | ((topt,f),(uu____36916,uu____36917,
                                                       (uu____36918,f_branch,t_branch)))
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
                                                    let uu____36995 =
                                                      type_leq g t1 t_branch
                                                       in
                                                    if uu____36995
                                                    then
                                                      FStar_Pervasives_Native.Some
                                                        t_branch
                                                    else
                                                      (let uu____37002 =
                                                         type_leq g t_branch
                                                           t1
                                                          in
                                                       if uu____37002
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
                                 (match uu____36798 with
                                  | (topt,f_match) ->
                                      let mlbranches2 =
                                        FStar_All.pipe_right mlbranches1
                                          (FStar_List.map
                                             (fun uu____37133  ->
                                                match uu____37133 with
                                                | (p,(wopt,uu____37174),
                                                   (b1,uu____37176,t1)) ->
                                                    let b2 =
                                                      match topt with
                                                      | FStar_Pervasives_Native.None
                                                           ->
                                                          FStar_Extraction_ML_Syntax.apply_obj_repr
                                                            b1 t1
                                                      | FStar_Pervasives_Native.Some
                                                          uu____37222 -> b1
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
                                      let uu____37233 =
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             t_match)
                                          (FStar_Extraction_ML_Syntax.MLE_Match
                                             (e1, mlbranches2))
                                         in
                                      (uu____37233, f_match, t_match)))))))

let (ind_discriminator_body :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlmodule1)
  =
  fun env  ->
    fun discName  ->
      fun constrName  ->
        let uu____37415 =
          let uu____37424 =
            FStar_TypeChecker_Env.lookup_lid
              env.FStar_Extraction_ML_UEnv.env_tcenv discName
             in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____37424  in
        match uu____37415 with
        | (uu____37465,fstar_disc_type) ->
            let wildcards =
              let uu____37483 =
                let uu____37484 = FStar_Syntax_Subst.compress fstar_disc_type
                   in
                uu____37484.FStar_Syntax_Syntax.n  in
              match uu____37483 with
              | FStar_Syntax_Syntax.Tm_arrow (binders,uu____37503) ->
                  let uu____37542 =
                    FStar_All.pipe_right binders
                      (FStar_List.filter
                         (fun uu___2_37596  ->
                            match uu___2_37596 with
                            | (uu____37609,FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____37610)) ->
                                true
                            | uu____37625 -> false))
                     in
                  FStar_All.pipe_right uu____37542
                    (FStar_List.map
                       (fun uu____37676  ->
                          let uu____37688 = fresh "_"  in
                          (uu____37688, FStar_Extraction_ML_Syntax.MLTY_Top)))
              | uu____37692 -> failwith "Discriminator must be a function"
               in
            let mlid = fresh "_discr_"  in
            let targ = FStar_Extraction_ML_Syntax.MLTY_Top  in
            let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top  in
            let discrBody =
              let uu____37713 =
                let uu____37714 =
                  let uu____37729 =
                    let uu____37736 =
                      let uu____37737 =
                        let uu____37761 =
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty targ)
                            (FStar_Extraction_ML_Syntax.MLE_Name ([], mlid))
                           in
                        let uu____37776 =
                          let uu____37793 =
                            let uu____37808 =
                              let uu____37809 =
                                let uu____37816 =
                                  FStar_Extraction_ML_Syntax.mlpath_of_lident
                                    constrName
                                   in
                                (uu____37816,
                                  [FStar_Extraction_ML_Syntax.MLP_Wild])
                                 in
                              FStar_Extraction_ML_Syntax.MLP_CTor uu____37809
                               in
                            let uu____37819 =
                              FStar_All.pipe_left
                                (FStar_Extraction_ML_Syntax.with_ty
                                   FStar_Extraction_ML_Syntax.ml_bool_ty)
                                (FStar_Extraction_ML_Syntax.MLE_Const
                                   (FStar_Extraction_ML_Syntax.MLC_Bool true))
                               in
                            (uu____37808, FStar_Pervasives_Native.None,
                              uu____37819)
                             in
                          let uu____37841 =
                            let uu____37858 =
                              let uu____37873 =
                                FStar_All.pipe_left
                                  (FStar_Extraction_ML_Syntax.with_ty
                                     FStar_Extraction_ML_Syntax.ml_bool_ty)
                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                     (FStar_Extraction_ML_Syntax.MLC_Bool
                                        false))
                                 in
                              (FStar_Extraction_ML_Syntax.MLP_Wild,
                                FStar_Pervasives_Native.None, uu____37873)
                               in
                            [uu____37858]  in
                          uu____37793 :: uu____37841  in
                        (uu____37761, uu____37776)  in
                      FStar_Extraction_ML_Syntax.MLE_Match uu____37737  in
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.ml_bool_ty) uu____37736
                     in
                  ((FStar_List.append wildcards [(mlid, targ)]), uu____37729)
                   in
                FStar_Extraction_ML_Syntax.MLE_Fun uu____37714  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty disc_ty) uu____37713
               in
            let uu____37988 =
              let uu____37989 =
                let uu____37998 =
                  let uu____38011 =
                    FStar_Extraction_ML_UEnv.convIdent
                      discName.FStar_Ident.ident
                     in
                  {
                    FStar_Extraction_ML_Syntax.mllb_name = uu____38011;
                    FStar_Extraction_ML_Syntax.mllb_tysc =
                      FStar_Pervasives_Native.None;
                    FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                    FStar_Extraction_ML_Syntax.mllb_def = discrBody;
                    FStar_Extraction_ML_Syntax.mllb_meta = [];
                    FStar_Extraction_ML_Syntax.print_typ = false
                  }  in
                [uu____37998]  in
              (FStar_Extraction_ML_Syntax.NonRec, uu____37989)  in
            FStar_Extraction_ML_Syntax.MLM_Let uu____37988
  