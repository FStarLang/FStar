open Prims
exception Un_extractable 
let (uu___is_Un_extractable : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Un_extractable  -> true | uu____65770 -> false
  
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
  'Auu____65839 .
    FStar_Ident.ident Prims.list ->
      'Auu____65839 Prims.list -> (Prims.string * 'Auu____65839) Prims.list
  =
  fun fs  ->
    fun vs  ->
      FStar_List.map2 (fun f  -> fun e  -> ((f.FStar_Ident.idText), e)) fs vs
  
let fail :
  'Auu____65882 .
    FStar_Range.range ->
      (FStar_Errors.raw_error * Prims.string) -> 'Auu____65882
  = fun r  -> fun err  -> FStar_Errors.raise_error err r 
let err_uninst :
  'Auu____65914 .
    FStar_Extraction_ML_UEnv.uenv ->
      FStar_Syntax_Syntax.term ->
        (Prims.string Prims.list * FStar_Extraction_ML_Syntax.mlty) ->
          FStar_Syntax_Syntax.term -> 'Auu____65914
  =
  fun env  ->
    fun t  ->
      fun uu____65940  ->
        fun app  ->
          match uu____65940 with
          | (vars,ty) ->
              let uu____65957 =
                let uu____65963 =
                  let uu____65965 = FStar_Syntax_Print.term_to_string t  in
                  let uu____65967 =
                    FStar_All.pipe_right vars (FStar_String.concat ", ")  in
                  let uu____65974 =
                    FStar_Extraction_ML_Code.string_of_mlty
                      env.FStar_Extraction_ML_UEnv.currentModule ty
                     in
                  let uu____65976 = FStar_Syntax_Print.term_to_string app  in
                  FStar_Util.format4
                    "Variable %s has a polymorphic type (forall %s. %s); expected it to be fully instantiated, but got %s"
                    uu____65965 uu____65967 uu____65974 uu____65976
                   in
                (FStar_Errors.Fatal_Uninstantiated, uu____65963)  in
              fail t.FStar_Syntax_Syntax.pos uu____65957
  
let err_ill_typed_application :
  'Auu____65995 'Auu____65996 .
    FStar_Extraction_ML_UEnv.uenv ->
      FStar_Syntax_Syntax.term ->
        FStar_Extraction_ML_Syntax.mlexpr ->
          (FStar_Syntax_Syntax.term * 'Auu____65995) Prims.list ->
            FStar_Extraction_ML_Syntax.mlty -> 'Auu____65996
  =
  fun env  ->
    fun t  ->
      fun mlhead  ->
        fun args  ->
          fun ty  ->
            let uu____66034 =
              let uu____66040 =
                let uu____66042 = FStar_Syntax_Print.term_to_string t  in
                let uu____66044 =
                  FStar_Extraction_ML_Code.string_of_mlexpr
                    env.FStar_Extraction_ML_UEnv.currentModule mlhead
                   in
                let uu____66046 =
                  FStar_Extraction_ML_Code.string_of_mlty
                    env.FStar_Extraction_ML_UEnv.currentModule ty
                   in
                let uu____66048 =
                  let uu____66050 =
                    FStar_All.pipe_right args
                      (FStar_List.map
                         (fun uu____66071  ->
                            match uu____66071 with
                            | (x,uu____66078) ->
                                FStar_Syntax_Print.term_to_string x))
                     in
                  FStar_All.pipe_right uu____66050 (FStar_String.concat " ")
                   in
                FStar_Util.format4
                  "Ill-typed application: source application is %s \n translated prefix to %s at type %s\n remaining args are %s\n"
                  uu____66042 uu____66044 uu____66046 uu____66048
                 in
              (FStar_Errors.Fatal_IllTyped, uu____66040)  in
            fail t.FStar_Syntax_Syntax.pos uu____66034
  
let err_ill_typed_erasure :
  'Auu____66095 .
    FStar_Extraction_ML_UEnv.uenv ->
      FStar_Range.range -> FStar_Extraction_ML_Syntax.mlty -> 'Auu____66095
  =
  fun env  ->
    fun pos  ->
      fun ty  ->
        let uu____66111 =
          let uu____66117 =
            let uu____66119 =
              FStar_Extraction_ML_Code.string_of_mlty
                env.FStar_Extraction_ML_UEnv.currentModule ty
               in
            FStar_Util.format1
              "Erased value found where a value of type %s was expected"
              uu____66119
             in
          (FStar_Errors.Fatal_IllTyped, uu____66117)  in
        fail pos uu____66111
  
let err_value_restriction :
  'Auu____66128 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> 'Auu____66128
  =
  fun t  ->
    let uu____66138 =
      let uu____66144 =
        let uu____66146 = FStar_Syntax_Print.tag_of_term t  in
        let uu____66148 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format2
          "Refusing to generalize because of the value restriction: (%s) %s"
          uu____66146 uu____66148
         in
      (FStar_Errors.Fatal_ValueRestriction, uu____66144)  in
    fail t.FStar_Syntax_Syntax.pos uu____66138
  
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
            let uu____66182 =
              let uu____66188 =
                let uu____66190 = FStar_Syntax_Print.term_to_string t  in
                let uu____66192 =
                  FStar_Extraction_ML_Code.string_of_mlty
                    env.FStar_Extraction_ML_UEnv.currentModule ty
                   in
                let uu____66194 = FStar_Extraction_ML_Util.eff_to_string f0
                   in
                let uu____66196 = FStar_Extraction_ML_Util.eff_to_string f1
                   in
                FStar_Util.format4
                  "for expression %s of type %s, Expected effect %s; got effect %s"
                  uu____66190 uu____66192 uu____66194 uu____66196
                 in
              (FStar_Errors.Warning_ExtractionUnexpectedEffect, uu____66188)
               in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____66182
  
let (effect_as_etag :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Ident.lident -> FStar_Extraction_ML_Syntax.e_tag)
  =
  let cache = FStar_Util.smap_create (Prims.parse_int "20")  in
  let rec delta_norm_eff g l =
    let uu____66224 = FStar_Util.smap_try_find cache l.FStar_Ident.str  in
    match uu____66224 with
    | FStar_Pervasives_Native.Some l1 -> l1
    | FStar_Pervasives_Native.None  ->
        let res =
          let uu____66229 =
            FStar_TypeChecker_Env.lookup_effect_abbrev
              g.FStar_Extraction_ML_UEnv.env_tcenv
              [FStar_Syntax_Syntax.U_zero] l
             in
          match uu____66229 with
          | FStar_Pervasives_Native.None  -> l
          | FStar_Pervasives_Native.Some (uu____66240,c) ->
              delta_norm_eff g (FStar_Syntax_Util.comp_effect_name c)
           in
        (FStar_Util.smap_add cache l.FStar_Ident.str res; res)
     in
  fun g  ->
    fun l  ->
      let l1 = delta_norm_eff g l  in
      let uu____66250 =
        FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid  in
      if uu____66250
      then FStar_Extraction_ML_Syntax.E_PURE
      else
        (let uu____66255 =
           FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GHOST_lid  in
         if uu____66255
         then FStar_Extraction_ML_Syntax.E_GHOST
         else
           (let ed_opt =
              FStar_TypeChecker_Env.effect_decl_opt
                g.FStar_Extraction_ML_UEnv.env_tcenv l1
               in
            match ed_opt with
            | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                let uu____66281 =
                  FStar_TypeChecker_Env.is_reifiable_effect
                    g.FStar_Extraction_ML_UEnv.env_tcenv
                    ed.FStar_Syntax_Syntax.mname
                   in
                if uu____66281
                then FStar_Extraction_ML_Syntax.E_PURE
                else FStar_Extraction_ML_Syntax.E_IMPURE
            | FStar_Pervasives_Native.None  ->
                FStar_Extraction_ML_Syntax.E_IMPURE))
  
let rec (is_arity :
  FStar_Extraction_ML_UEnv.uenv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t  in
      let uu____66305 =
        let uu____66306 = FStar_Syntax_Subst.compress t1  in
        uu____66306.FStar_Syntax_Syntax.n  in
      match uu____66305 with
      | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____66312 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_ascribed uu____66337 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_meta uu____66366 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____66376 = FStar_Syntax_Util.unfold_lazy i  in
          is_arity env uu____66376
      | FStar_Syntax_Syntax.Tm_uvar uu____66377 -> false
      | FStar_Syntax_Syntax.Tm_constant uu____66391 -> false
      | FStar_Syntax_Syntax.Tm_name uu____66393 -> false
      | FStar_Syntax_Syntax.Tm_quoted uu____66395 -> false
      | FStar_Syntax_Syntax.Tm_bvar uu____66403 -> false
      | FStar_Syntax_Syntax.Tm_type uu____66405 -> true
      | FStar_Syntax_Syntax.Tm_arrow (uu____66407,c) ->
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
           | FStar_Pervasives_Native.Some (uu____66443,t2) -> is_arity env t2)
      | FStar_Syntax_Syntax.Tm_app uu____66449 ->
          let uu____66466 = FStar_Syntax_Util.head_and_args t1  in
          (match uu____66466 with | (head1,uu____66485) -> is_arity env head1)
      | FStar_Syntax_Syntax.Tm_uinst (head1,uu____66511) ->
          is_arity env head1
      | FStar_Syntax_Syntax.Tm_refine (x,uu____66517) ->
          is_arity env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_abs (uu____66522,body,uu____66524) ->
          is_arity env body
      | FStar_Syntax_Syntax.Tm_let (uu____66549,body) -> is_arity env body
      | FStar_Syntax_Syntax.Tm_match (uu____66569,branches) ->
          (match branches with
           | (uu____66608,uu____66609,e)::uu____66611 -> is_arity env e
           | uu____66658 -> false)
  
let rec (is_type_aux :
  FStar_Extraction_ML_UEnv.uenv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____66690 ->
          let uu____66713 =
            let uu____66715 = FStar_Syntax_Print.tag_of_term t1  in
            FStar_Util.format1 "Impossible: %s" uu____66715  in
          failwith uu____66713
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____66719 =
            let uu____66721 = FStar_Syntax_Print.tag_of_term t1  in
            FStar_Util.format1 "Impossible: %s" uu____66721  in
          failwith uu____66719
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____66726 = FStar_Syntax_Util.unfold_lazy i  in
          is_type_aux env uu____66726
      | FStar_Syntax_Syntax.Tm_constant uu____66727 -> false
      | FStar_Syntax_Syntax.Tm_type uu____66729 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____66731 -> true
      | FStar_Syntax_Syntax.Tm_arrow uu____66739 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.failwith_lid ->
          false
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Extraction_ML_UEnv.is_type_name env fv
      | FStar_Syntax_Syntax.Tm_uvar
          ({ FStar_Syntax_Syntax.ctx_uvar_head = uu____66758;
             FStar_Syntax_Syntax.ctx_uvar_gamma = uu____66759;
             FStar_Syntax_Syntax.ctx_uvar_binders = uu____66760;
             FStar_Syntax_Syntax.ctx_uvar_typ = t2;
             FStar_Syntax_Syntax.ctx_uvar_reason = uu____66762;
             FStar_Syntax_Syntax.ctx_uvar_should_check = uu____66763;
             FStar_Syntax_Syntax.ctx_uvar_range = uu____66764;
             FStar_Syntax_Syntax.ctx_uvar_meta = uu____66765;_},s)
          ->
          let uu____66814 = FStar_Syntax_Subst.subst' s t2  in
          is_arity env uu____66814
      | FStar_Syntax_Syntax.Tm_bvar
          { FStar_Syntax_Syntax.ppname = uu____66815;
            FStar_Syntax_Syntax.index = uu____66816;
            FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_name
          { FStar_Syntax_Syntax.ppname = uu____66821;
            FStar_Syntax_Syntax.index = uu____66822;
            FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____66828,uu____66829) ->
          is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____66871) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____66878) ->
          let uu____66903 = FStar_Syntax_Subst.open_term bs body  in
          (match uu____66903 with
           | (uu____66909,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
          let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
          let uu____66929 =
            let uu____66934 =
              let uu____66935 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____66935]  in
            FStar_Syntax_Subst.open_term uu____66934 body  in
          (match uu____66929 with
           | (uu____66955,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_let ((uu____66957,lbs),body) ->
          let uu____66977 = FStar_Syntax_Subst.open_let_rec lbs body  in
          (match uu____66977 with
           | (uu____66985,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_match (uu____66991,branches) ->
          (match branches with
           | b::uu____67031 ->
               let uu____67076 = FStar_Syntax_Subst.open_branch b  in
               (match uu____67076 with
                | (uu____67078,uu____67079,e) -> is_type_aux env e)
           | uu____67097 -> false)
      | FStar_Syntax_Syntax.Tm_quoted uu____67115 -> false
      | FStar_Syntax_Syntax.Tm_meta (t2,uu____67124) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_app (head1,uu____67130) ->
          is_type_aux env head1
  
let (is_type :
  FStar_Extraction_ML_UEnv.uenv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      FStar_Extraction_ML_UEnv.debug env
        (fun uu____67171  ->
           let uu____67172 = FStar_Syntax_Print.tag_of_term t  in
           let uu____67174 = FStar_Syntax_Print.term_to_string t  in
           FStar_Util.print2 "checking is_type (%s) %s\n" uu____67172
             uu____67174);
      (let b = is_type_aux env t  in
       FStar_Extraction_ML_UEnv.debug env
         (fun uu____67183  ->
            if b
            then
              let uu____67185 = FStar_Syntax_Print.term_to_string t  in
              let uu____67187 = FStar_Syntax_Print.tag_of_term t  in
              FStar_Util.print2 "yes, is_type %s (%s)\n" uu____67185
                uu____67187
            else
              (let uu____67192 = FStar_Syntax_Print.term_to_string t  in
               let uu____67194 = FStar_Syntax_Print.tag_of_term t  in
               FStar_Util.print2 "not a type %s (%s)\n" uu____67192
                 uu____67194));
       b)
  
let is_type_binder :
  'Auu____67204 .
    FStar_Extraction_ML_UEnv.uenv ->
      (FStar_Syntax_Syntax.bv * 'Auu____67204) -> Prims.bool
  =
  fun env  ->
    fun x  ->
      is_arity env (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
  
let (is_constructor : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____67231 =
      let uu____67232 = FStar_Syntax_Subst.compress t  in
      uu____67232.FStar_Syntax_Syntax.n  in
    match uu____67231 with
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____67236;
          FStar_Syntax_Syntax.fv_delta = uu____67237;
          FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
            (FStar_Syntax_Syntax.Data_ctor );_}
        -> true
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____67239;
          FStar_Syntax_Syntax.fv_delta = uu____67240;
          FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
            (FStar_Syntax_Syntax.Record_ctor uu____67241);_}
        -> true
    | uu____67249 -> false
  
let rec (is_fstar_value : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____67258 =
      let uu____67259 = FStar_Syntax_Subst.compress t  in
      uu____67259.FStar_Syntax_Syntax.n  in
    match uu____67258 with
    | FStar_Syntax_Syntax.Tm_constant uu____67263 -> true
    | FStar_Syntax_Syntax.Tm_bvar uu____67265 -> true
    | FStar_Syntax_Syntax.Tm_fvar uu____67267 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____67269 -> true
    | FStar_Syntax_Syntax.Tm_app (head1,args) ->
        let uu____67315 = is_constructor head1  in
        if uu____67315
        then
          FStar_All.pipe_right args
            (FStar_List.for_all
               (fun uu____67337  ->
                  match uu____67337 with
                  | (te,uu____67346) -> is_fstar_value te))
        else false
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____67355) -> is_fstar_value t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____67361,uu____67362) ->
        is_fstar_value t1
    | uu____67403 -> false
  
let rec (is_ml_value : FStar_Extraction_ML_Syntax.mlexpr -> Prims.bool) =
  fun e  ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_Const uu____67413 -> true
    | FStar_Extraction_ML_Syntax.MLE_Var uu____67415 -> true
    | FStar_Extraction_ML_Syntax.MLE_Name uu____67418 -> true
    | FStar_Extraction_ML_Syntax.MLE_Fun uu____67420 -> true
    | FStar_Extraction_ML_Syntax.MLE_CTor (uu____67433,exps) ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Tuple exps ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Record (uu____67442,fields) ->
        FStar_Util.for_all
          (fun uu____67472  ->
             match uu____67472 with | (uu____67479,e1) -> is_ml_value e1)
          fields
    | FStar_Extraction_ML_Syntax.MLE_TApp (h,uu____67484) -> is_ml_value h
    | uu____67489 -> false
  
let (fresh : Prims.string -> Prims.string) =
  let c = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun x  ->
    FStar_Util.incr c;
    (let uu____67507 =
       let uu____67509 = FStar_ST.op_Bang c  in
       FStar_Util.string_of_int uu____67509  in
     Prims.op_Hat x uu____67507)
  
let (normalize_abs : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t0  ->
    let rec aux bs t copt =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_abs (bs',body,copt1) ->
          aux (FStar_List.append bs bs') body copt1
      | uu____67612 ->
          let e' = FStar_Syntax_Util.unascribe t1  in
          let uu____67614 = FStar_Syntax_Util.is_fun e'  in
          if uu____67614
          then aux bs e' copt
          else FStar_Syntax_Util.abs bs e' copt
       in
    aux [] t0 FStar_Pervasives_Native.None
  
let (unit_binder : FStar_Syntax_Syntax.binder) =
  let uu____67628 =
    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
      FStar_Syntax_Syntax.t_unit
     in
  FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____67628 
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
      (let uu____67719 = FStar_List.hd l  in
       match uu____67719 with
       | (p1,w1,e1) ->
           let uu____67754 =
             let uu____67763 = FStar_List.tl l  in FStar_List.hd uu____67763
              in
           (match uu____67754 with
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
                 | uu____67847 -> def)))
  
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
      let uu____67886 = FStar_Extraction_ML_Util.doms_and_cod t  in
      match uu____67886 with
      | (ts,r) ->
          if ts = []
          then e
          else
            (let vs = FStar_List.map (fun uu____67910  -> fresh "a") ts  in
             let vs_ts = FStar_List.zip vs ts  in
             let vs_es =
               let uu____67924 = FStar_List.zip vs ts  in
               FStar_List.map
                 (fun uu____67941  ->
                    match uu____67941 with
                    | (v1,t1) ->
                        FStar_Extraction_ML_Syntax.with_ty t1
                          (FStar_Extraction_ML_Syntax.MLE_Var v1))
                 uu____67924
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
      let uu____67972 = FStar_Extraction_ML_Util.doms_and_cod t  in
      match uu____67972 with
      | (ts,r) ->
          let body r1 =
            let r2 =
              let uu____67992 = FStar_Extraction_ML_Util.udelta_unfold g r1
                 in
              match uu____67992 with
              | FStar_Pervasives_Native.None  -> r1
              | FStar_Pervasives_Native.Some r2 -> r2  in
            match r2 with
            | FStar_Extraction_ML_Syntax.MLTY_Erased  ->
                FStar_Extraction_ML_Syntax.ml_unit
            | FStar_Extraction_ML_Syntax.MLTY_Top  ->
                FStar_Extraction_ML_Syntax.apply_obj_repr
                  FStar_Extraction_ML_Syntax.ml_unit
                  FStar_Extraction_ML_Syntax.MLTY_Erased
            | uu____67996 ->
                FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty r2)
                  (FStar_Extraction_ML_Syntax.MLE_Coerce
                     (FStar_Extraction_ML_Syntax.ml_unit,
                       FStar_Extraction_ML_Syntax.MLTY_Erased, r2))
             in
          if ts = []
          then body r
          else
            (let vs = FStar_List.map (fun uu____68008  -> fresh "a") ts  in
             let vs_ts = FStar_List.zip vs ts  in
             let uu____68019 =
               let uu____68020 =
                 let uu____68032 = body r  in (vs_ts, uu____68032)  in
               FStar_Extraction_ML_Syntax.MLE_Fun uu____68020  in
             FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t)
               uu____68019)
  
let (maybe_eta_expand :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun expect  ->
    fun e  ->
      let uu____68051 =
        (FStar_Options.ml_no_eta_expand_coertions ()) ||
          (let uu____68054 = FStar_Options.codegen ()  in
           uu____68054 = (FStar_Pervasives_Native.Some FStar_Options.Kremlin))
         in
      if uu____68051 then e else eta_expand expect e
  
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
            | uu____68132 ->
                FStar_Extraction_ML_Syntax.MLE_Fun ([binder], body)
             in
          let rec aux e1 ty1 expect1 =
            let coerce_branch uu____68187 =
              match uu____68187 with
              | (pat,w,b) ->
                  let uu____68211 = aux b ty1 expect1  in
                  (pat, w, uu____68211)
               in
            match ((e1.FStar_Extraction_ML_Syntax.expr), ty1, expect1) with
            | (FStar_Extraction_ML_Syntax.MLE_Fun
               (arg::rest,body),FStar_Extraction_ML_Syntax.MLTY_Fun
               (t0,uu____68218,t1),FStar_Extraction_ML_Syntax.MLTY_Fun
               (s0,uu____68221,s1)) ->
                let body1 =
                  match rest with
                  | [] -> body
                  | uu____68253 ->
                      FStar_Extraction_ML_Syntax.with_ty t1
                        (FStar_Extraction_ML_Syntax.MLE_Fun (rest, body))
                   in
                let body2 = aux body1 t1 s1  in
                let uu____68269 = type_leq g s0 t0  in
                if uu____68269
                then
                  FStar_Extraction_ML_Syntax.with_ty expect1
                    (mk_fun arg body2)
                else
                  (let lb =
                     let uu____68275 =
                       let uu____68276 =
                         let uu____68277 =
                           let uu____68284 =
                             FStar_All.pipe_left
                               (FStar_Extraction_ML_Syntax.with_ty s0)
                               (FStar_Extraction_ML_Syntax.MLE_Var
                                  (FStar_Pervasives_Native.fst arg))
                              in
                           (uu____68284, s0, t0)  in
                         FStar_Extraction_ML_Syntax.MLE_Coerce uu____68277
                          in
                       FStar_Extraction_ML_Syntax.with_ty t0 uu____68276  in
                     {
                       FStar_Extraction_ML_Syntax.mllb_name =
                         (FStar_Pervasives_Native.fst arg);
                       FStar_Extraction_ML_Syntax.mllb_tysc =
                         (FStar_Pervasives_Native.Some ([], t0));
                       FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                       FStar_Extraction_ML_Syntax.mllb_def = uu____68275;
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
               (lbs,body),uu____68303,uu____68304) ->
                let uu____68317 =
                  let uu____68318 =
                    let uu____68329 = aux body ty1 expect1  in
                    (lbs, uu____68329)  in
                  FStar_Extraction_ML_Syntax.MLE_Let uu____68318  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____68317
            | (FStar_Extraction_ML_Syntax.MLE_Match
               (s,branches),uu____68338,uu____68339) ->
                let uu____68360 =
                  let uu____68361 =
                    let uu____68376 = FStar_List.map coerce_branch branches
                       in
                    (s, uu____68376)  in
                  FStar_Extraction_ML_Syntax.MLE_Match uu____68361  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____68360
            | (FStar_Extraction_ML_Syntax.MLE_If
               (s,b1,b2_opt),uu____68416,uu____68417) ->
                let uu____68422 =
                  let uu____68423 =
                    let uu____68432 = aux b1 ty1 expect1  in
                    let uu____68433 =
                      FStar_Util.map_opt b2_opt
                        (fun b2  -> aux b2 ty1 expect1)
                       in
                    (s, uu____68432, uu____68433)  in
                  FStar_Extraction_ML_Syntax.MLE_If uu____68423  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____68422
            | (FStar_Extraction_ML_Syntax.MLE_Seq es,uu____68441,uu____68442)
                ->
                let uu____68445 = FStar_Util.prefix es  in
                (match uu____68445 with
                 | (prefix1,last1) ->
                     let uu____68458 =
                       let uu____68459 =
                         let uu____68462 =
                           let uu____68465 = aux last1 ty1 expect1  in
                           [uu____68465]  in
                         FStar_List.append prefix1 uu____68462  in
                       FStar_Extraction_ML_Syntax.MLE_Seq uu____68459  in
                     FStar_All.pipe_left
                       (FStar_Extraction_ML_Syntax.with_ty expect1)
                       uu____68458)
            | (FStar_Extraction_ML_Syntax.MLE_Try
               (s,branches),uu____68468,uu____68469) ->
                let uu____68490 =
                  let uu____68491 =
                    let uu____68506 = FStar_List.map coerce_branch branches
                       in
                    (s, uu____68506)  in
                  FStar_Extraction_ML_Syntax.MLE_Try uu____68491  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____68490
            | uu____68543 ->
                FStar_Extraction_ML_Syntax.with_ty expect1
                  (FStar_Extraction_ML_Syntax.MLE_Coerce (e1, ty1, expect1))
             in
          aux e ty expect
  
let maybe_coerce :
  'Auu____68563 .
    'Auu____68563 ->
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
            let uu____68590 =
              type_leq_c g (FStar_Pervasives_Native.Some e) ty1 expect  in
            match uu____68590 with
            | (true ,FStar_Pervasives_Native.Some e') -> e'
            | uu____68603 ->
                (match ty1 with
                 | FStar_Extraction_ML_Syntax.MLTY_Erased  ->
                     default_value_for_ty g expect
                 | uu____68611 ->
                     let uu____68612 =
                       let uu____68614 =
                         FStar_Extraction_ML_Util.erase_effect_annotations
                           ty1
                          in
                       let uu____68615 =
                         FStar_Extraction_ML_Util.erase_effect_annotations
                           expect
                          in
                       type_leq g uu____68614 uu____68615  in
                     if uu____68612
                     then
                       (FStar_Extraction_ML_UEnv.debug g
                          (fun uu____68621  ->
                             let uu____68622 =
                               FStar_Extraction_ML_Code.string_of_mlexpr
                                 g.FStar_Extraction_ML_UEnv.currentModule e
                                in
                             let uu____68624 =
                               FStar_Extraction_ML_Code.string_of_mlty
                                 g.FStar_Extraction_ML_UEnv.currentModule ty1
                                in
                             FStar_Util.print2
                               "\n Effect mismatch on type of %s : %s\n"
                               uu____68622 uu____68624);
                        e)
                     else
                       (FStar_Extraction_ML_UEnv.debug g
                          (fun uu____68634  ->
                             let uu____68635 =
                               FStar_Extraction_ML_Code.string_of_mlexpr
                                 g.FStar_Extraction_ML_UEnv.currentModule e
                                in
                             let uu____68637 =
                               FStar_Extraction_ML_Code.string_of_mlty
                                 g.FStar_Extraction_ML_UEnv.currentModule ty1
                                in
                             let uu____68639 =
                               FStar_Extraction_ML_Code.string_of_mlty
                                 g.FStar_Extraction_ML_UEnv.currentModule
                                 expect
                                in
                             FStar_Util.print3
                               "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n"
                               uu____68635 uu____68637 uu____68639);
                        (let uu____68642 = apply_coercion g e ty1 expect  in
                         maybe_eta_expand expect uu____68642)))
  
let (bv_as_mlty :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun bv  ->
      let uu____68654 = FStar_Extraction_ML_UEnv.lookup_bv g bv  in
      match uu____68654 with
      | FStar_Util.Inl ty_b -> ty_b.FStar_Extraction_ML_UEnv.ty_b_ty
      | uu____68656 -> FStar_Extraction_ML_Syntax.MLTY_Top
  
let (extraction_norm_steps : FStar_TypeChecker_Env.step Prims.list) =
  [FStar_TypeChecker_Env.AllowUnboundUniverses;
  FStar_TypeChecker_Env.EraseUniverses;
  FStar_TypeChecker_Env.Inlining;
  FStar_TypeChecker_Env.Eager_unfolding;
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
    | FStar_Syntax_Syntax.Total uu____68674 -> c
    | FStar_Syntax_Syntax.GTotal uu____68683 -> c
    | FStar_Syntax_Syntax.Comp ct ->
        let effect_args =
          FStar_List.map
            (fun uu____68719  ->
               match uu____68719 with
               | (uu____68734,aq) -> (FStar_Syntax_Syntax.t_unit, aq))
            ct.FStar_Syntax_Syntax.effect_args
           in
        let ct1 =
          let uu___1131_68747 = ct  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___1131_68747.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___1131_68747.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ =
              (uu___1131_68747.FStar_Syntax_Syntax.result_typ);
            FStar_Syntax_Syntax.effect_args = effect_args;
            FStar_Syntax_Syntax.flags =
              (uu___1131_68747.FStar_Syntax_Syntax.flags)
          }  in
        let c1 =
          let uu___1134_68751 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
            FStar_Syntax_Syntax.pos =
              (uu___1134_68751.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___1134_68751.FStar_Syntax_Syntax.vars)
          }  in
        c1
  
let rec (translate_term_to_mlty :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun t0  ->
      let arg_as_mlty g1 uu____68800 =
        match uu____68800 with
        | (a,uu____68808) ->
            let uu____68813 = is_type g1 a  in
            if uu____68813
            then translate_term_to_mlty g1 a
            else FStar_Extraction_ML_UEnv.erasedContent
         in
      let fv_app_as_mlty g1 fv args =
        let uu____68834 =
          let uu____68836 = FStar_Extraction_ML_UEnv.is_fv_type g1 fv  in
          Prims.op_Negation uu____68836  in
        if uu____68834
        then FStar_Extraction_ML_Syntax.MLTY_Top
        else
          (let uu____68841 =
             let uu____68856 =
               FStar_TypeChecker_Env.lookup_lid
                 g1.FStar_Extraction_ML_UEnv.env_tcenv
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             match uu____68856 with
             | ((uu____68879,fvty),uu____68881) ->
                 let fvty1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Env.UnfoldUntil
                        FStar_Syntax_Syntax.delta_constant]
                     g1.FStar_Extraction_ML_UEnv.env_tcenv fvty
                    in
                 FStar_Syntax_Util.arrow_formals fvty1
              in
           match uu____68841 with
           | (formals,uu____68888) ->
               let mlargs = FStar_List.map (arg_as_mlty g1) args  in
               let mlargs1 =
                 let n_args = FStar_List.length args  in
                 if (FStar_List.length formals) > n_args
                 then
                   let uu____68941 = FStar_Util.first_N n_args formals  in
                   match uu____68941 with
                   | (uu____68970,rest) ->
                       let uu____69004 =
                         FStar_List.map
                           (fun uu____69014  ->
                              FStar_Extraction_ML_UEnv.erasedContent) rest
                          in
                       FStar_List.append mlargs uu____69004
                 else mlargs  in
               let nm =
                 let uu____69024 =
                   FStar_Extraction_ML_UEnv.maybe_mangle_type_projector g1 fv
                    in
                 match uu____69024 with
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
        | FStar_Syntax_Syntax.Tm_type uu____69042 ->
            FStar_Extraction_ML_Syntax.MLTY_Erased
        | FStar_Syntax_Syntax.Tm_bvar uu____69043 ->
            let uu____69044 =
              let uu____69046 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____69046
               in
            failwith uu____69044
        | FStar_Syntax_Syntax.Tm_delayed uu____69049 ->
            let uu____69072 =
              let uu____69074 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____69074
               in
            failwith uu____69072
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____69077 =
              let uu____69079 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____69079
               in
            failwith uu____69077
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____69083 = FStar_Syntax_Util.unfold_lazy i  in
            translate_term_to_mlty env uu____69083
        | FStar_Syntax_Syntax.Tm_constant uu____69084 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_quoted uu____69085 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_uvar uu____69092 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_meta (t2,uu____69106) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____69111;
               FStar_Syntax_Syntax.index = uu____69112;
               FStar_Syntax_Syntax.sort = t2;_},uu____69114)
            -> translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_uinst (t2,uu____69123) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____69129,uu____69130) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
        | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv []
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let uu____69203 = FStar_Syntax_Subst.open_comp bs c  in
            (match uu____69203 with
             | (bs1,c1) ->
                 let uu____69210 = binders_as_ml_binders env bs1  in
                 (match uu____69210 with
                  | (mlbs,env1) ->
                      let t_ret =
                        let eff =
                          FStar_TypeChecker_Env.norm_eff_name
                            env1.FStar_Extraction_ML_UEnv.env_tcenv
                            (FStar_Syntax_Util.comp_effect_name c1)
                           in
                        let c2 = comp_no_args c1  in
                        let uu____69243 =
                          let uu____69250 =
                            FStar_TypeChecker_Env.effect_decl_opt
                              env1.FStar_Extraction_ML_UEnv.env_tcenv eff
                             in
                          FStar_Util.must uu____69250  in
                        match uu____69243 with
                        | (ed,qualifiers) ->
                            let uu____69271 =
                              FStar_TypeChecker_Env.is_reifiable_effect
                                g.FStar_Extraction_ML_UEnv.env_tcenv
                                ed.FStar_Syntax_Syntax.mname
                               in
                            if uu____69271
                            then
                              let t2 =
                                FStar_TypeChecker_Env.reify_comp
                                  env1.FStar_Extraction_ML_UEnv.env_tcenv c2
                                  FStar_Syntax_Syntax.U_unknown
                                 in
                              (FStar_Extraction_ML_UEnv.debug env1
                                 (fun uu____69279  ->
                                    let uu____69280 =
                                      FStar_Syntax_Print.comp_to_string c2
                                       in
                                    let uu____69282 =
                                      FStar_Syntax_Print.term_to_string t2
                                       in
                                    FStar_Util.print2
                                      "Translating comp type %s as %s\n"
                                      uu____69280 uu____69282);
                               (let res = translate_term_to_mlty env1 t2  in
                                FStar_Extraction_ML_UEnv.debug env1
                                  (fun uu____69291  ->
                                     let uu____69292 =
                                       FStar_Syntax_Print.comp_to_string c2
                                        in
                                     let uu____69294 =
                                       FStar_Syntax_Print.term_to_string t2
                                        in
                                     let uu____69296 =
                                       FStar_Extraction_ML_Code.string_of_mlty
                                         env1.FStar_Extraction_ML_UEnv.currentModule
                                         res
                                        in
                                     FStar_Util.print3
                                       "Translated comp type %s as %s ... to %s\n"
                                       uu____69292 uu____69294 uu____69296);
                                res))
                            else
                              translate_term_to_mlty env1
                                (FStar_Syntax_Util.comp_result c2)
                         in
                      let erase =
                        effect_as_etag env1
                          (FStar_Syntax_Util.comp_effect_name c1)
                         in
                      let uu____69302 =
                        FStar_List.fold_right
                          (fun uu____69322  ->
                             fun uu____69323  ->
                               match (uu____69322, uu____69323) with
                               | ((uu____69346,t2),(tag,t')) ->
                                   (FStar_Extraction_ML_Syntax.E_PURE,
                                     (FStar_Extraction_ML_Syntax.MLTY_Fun
                                        (t2, tag, t')))) mlbs (erase, t_ret)
                         in
                      (match uu____69302 with | (uu____69361,t2) -> t2)))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let res =
              let uu____69390 =
                let uu____69391 = FStar_Syntax_Util.un_uinst head1  in
                uu____69391.FStar_Syntax_Syntax.n  in
              match uu____69390 with
              | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv args
              | FStar_Syntax_Syntax.Tm_app (head2,args') ->
                  let uu____69422 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_app
                         (head2, (FStar_List.append args' args)))
                      FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                     in
                  translate_term_to_mlty env uu____69422
              | uu____69443 -> FStar_Extraction_ML_UEnv.unknownType  in
            res
        | FStar_Syntax_Syntax.Tm_abs (bs,ty,uu____69446) ->
            let uu____69471 = FStar_Syntax_Subst.open_term bs ty  in
            (match uu____69471 with
             | (bs1,ty1) ->
                 let uu____69478 = binders_as_ml_binders env bs1  in
                 (match uu____69478 with
                  | (bts,env1) -> translate_term_to_mlty env1 ty1))
        | FStar_Syntax_Syntax.Tm_let uu____69506 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_match uu____69520 ->
            FStar_Extraction_ML_UEnv.unknownType
         in
      let rec is_top_ty t =
        match t with
        | FStar_Extraction_ML_Syntax.MLTY_Top  -> true
        | FStar_Extraction_ML_Syntax.MLTY_Named uu____69552 ->
            let uu____69559 = FStar_Extraction_ML_Util.udelta_unfold g t  in
            (match uu____69559 with
             | FStar_Pervasives_Native.None  -> false
             | FStar_Pervasives_Native.Some t1 -> is_top_ty t1)
        | uu____69565 -> false  in
      let uu____69567 =
        FStar_TypeChecker_Util.must_erase_for_extraction
          g.FStar_Extraction_ML_UEnv.env_tcenv t0
         in
      if uu____69567
      then FStar_Extraction_ML_Syntax.MLTY_Erased
      else
        (let mlt = aux g t0  in
         let uu____69573 = is_top_ty mlt  in
         if uu____69573 then FStar_Extraction_ML_Syntax.MLTY_Top else mlt)

and (binders_as_ml_binders :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.binders ->
      ((FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)
        Prims.list * FStar_Extraction_ML_UEnv.uenv))
  =
  fun g  ->
    fun bs  ->
      let uu____69591 =
        FStar_All.pipe_right bs
          (FStar_List.fold_left
             (fun uu____69647  ->
                fun b  ->
                  match uu____69647 with
                  | (ml_bs,env) ->
                      let uu____69693 = is_type_binder g b  in
                      if uu____69693
                      then
                        let b1 = FStar_Pervasives_Native.fst b  in
                        let env1 =
                          FStar_Extraction_ML_UEnv.extend_ty env b1
                            (FStar_Pervasives_Native.Some
                               FStar_Extraction_ML_Syntax.MLTY_Top)
                           in
                        let ml_b =
                          let uu____69719 =
                            FStar_Extraction_ML_UEnv.bv_as_ml_termvar b1  in
                          (uu____69719,
                            FStar_Extraction_ML_Syntax.ml_unit_ty)
                           in
                        ((ml_b :: ml_bs), env1)
                      else
                        (let b1 = FStar_Pervasives_Native.fst b  in
                         let t =
                           translate_term_to_mlty env
                             b1.FStar_Syntax_Syntax.sort
                            in
                         let uu____69740 =
                           FStar_Extraction_ML_UEnv.extend_bv env b1 
                             ([], t) false false false
                            in
                         match uu____69740 with
                         | (env1,b2,uu____69765) ->
                             let ml_b =
                               let uu____69774 =
                                 FStar_Extraction_ML_UEnv.removeTick b2  in
                               (uu____69774, t)  in
                             ((ml_b :: ml_bs), env1))) ([], g))
         in
      match uu____69591 with | (ml_bs,env) -> ((FStar_List.rev ml_bs), env)

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
      | (FStar_Extraction_ML_Syntax.MLE_Seq es1,uu____69870) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (FStar_List.append es1 [e2])
      | (uu____69873,FStar_Extraction_ML_Syntax.MLE_Seq es2) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (e1 :: es2)
      | uu____69877 -> FStar_Extraction_ML_Syntax.MLE_Seq [e1; e2]
  
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
                    | uu____69911 when
                        (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
                          =
                          FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr
                        -> body.FStar_Extraction_ML_Syntax.expr
                    | uu____69912 ->
                        mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def
                          body)
             | uu____69913 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body))
        | uu____69922 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body)
  
let (resugar_pat :
  FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option ->
    FStar_Extraction_ML_Syntax.mlpattern ->
      FStar_Extraction_ML_Syntax.mlpattern)
  =
  fun q  ->
    fun p  ->
      match p with
      | FStar_Extraction_ML_Syntax.MLP_CTor (d,pats) ->
          let uu____69950 = FStar_Extraction_ML_Util.is_xtuple d  in
          (match uu____69950 with
           | FStar_Pervasives_Native.Some n1 ->
               FStar_Extraction_ML_Syntax.MLP_Tuple pats
           | uu____69957 ->
               (match q with
                | FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Record_ctor (ty,fns)) ->
                    let path =
                      FStar_List.map FStar_Ident.text_of_id ty.FStar_Ident.ns
                       in
                    let fs = record_fields fns pats  in
                    FStar_Extraction_ML_Syntax.MLP_Record (path, fs)
                | uu____69990 -> p))
      | uu____69993 -> p
  
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
                       (fun uu____70095  ->
                          let uu____70096 =
                            FStar_Extraction_ML_Code.string_of_mlty
                              g.FStar_Extraction_ML_UEnv.currentModule t'
                             in
                          let uu____70098 =
                            FStar_Extraction_ML_Code.string_of_mlty
                              g.FStar_Extraction_ML_UEnv.currentModule t
                             in
                          FStar_Util.print2
                            "Expected pattern type %s; got pattern type %s\n"
                            uu____70096 uu____70098)
                   else ();
                   ok)
               in
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int
                (c,swopt)) when
                let uu____70134 = FStar_Options.codegen ()  in
                uu____70134 <>
                  (FStar_Pervasives_Native.Some FStar_Options.Kremlin)
                ->
                let uu____70139 =
                  match swopt with
                  | FStar_Pervasives_Native.None  ->
                      let uu____70152 =
                        let uu____70153 =
                          let uu____70154 =
                            FStar_Extraction_ML_Util.mlconst_of_const
                              p.FStar_Syntax_Syntax.p
                              (FStar_Const.Const_int
                                 (c, FStar_Pervasives_Native.None))
                             in
                          FStar_Extraction_ML_Syntax.MLE_Const uu____70154
                           in
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.ml_int_ty)
                          uu____70153
                         in
                      (uu____70152, FStar_Extraction_ML_Syntax.ml_int_ty)
                  | FStar_Pervasives_Native.Some sw ->
                      let source_term =
                        FStar_ToSyntax_ToSyntax.desugar_machine_integer
                          (g.FStar_Extraction_ML_UEnv.env_tcenv).FStar_TypeChecker_Env.dsenv
                          c sw FStar_Range.dummyRange
                         in
                      let uu____70176 = term_as_mlexpr g source_term  in
                      (match uu____70176 with
                       | (mlterm,uu____70188,mlty) -> (mlterm, mlty))
                   in
                (match uu____70139 with
                 | (mlc,ml_ty) ->
                     let x = FStar_Extraction_ML_Syntax.gensym ()  in
                     let when_clause =
                       let uu____70210 =
                         let uu____70211 =
                           let uu____70218 =
                             let uu____70221 =
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty ml_ty)
                                 (FStar_Extraction_ML_Syntax.MLE_Var x)
                                in
                             [uu____70221; mlc]  in
                           (FStar_Extraction_ML_Util.prims_op_equality,
                             uu____70218)
                            in
                         FStar_Extraction_ML_Syntax.MLE_App uu____70211  in
                       FStar_All.pipe_left
                         (FStar_Extraction_ML_Syntax.with_ty
                            FStar_Extraction_ML_Syntax.ml_bool_ty)
                         uu____70210
                        in
                     let uu____70224 = ok ml_ty  in
                     (g,
                       (FStar_Pervasives_Native.Some
                          ((FStar_Extraction_ML_Syntax.MLP_Var x),
                            [when_clause])), uu____70224))
            | FStar_Syntax_Syntax.Pat_constant s ->
                let t =
                  FStar_TypeChecker_TcTerm.tc_constant
                    g.FStar_Extraction_ML_UEnv.env_tcenv
                    FStar_Range.dummyRange s
                   in
                let mlty = term_as_mlty g t  in
                let uu____70246 =
                  let uu____70255 =
                    let uu____70262 =
                      let uu____70263 =
                        FStar_Extraction_ML_Util.mlconst_of_const
                          p.FStar_Syntax_Syntax.p s
                         in
                      FStar_Extraction_ML_Syntax.MLP_Const uu____70263  in
                    (uu____70262, [])  in
                  FStar_Pervasives_Native.Some uu____70255  in
                let uu____70272 = ok mlty  in (g, uu____70246, uu____70272)
            | FStar_Syntax_Syntax.Pat_var x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort  in
                let uu____70285 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp
                   in
                (match uu____70285 with
                 | (g1,x1,uu____70313) ->
                     let uu____70316 = ok mlty  in
                     (g1,
                       (if imp
                        then FStar_Pervasives_Native.None
                        else
                          FStar_Pervasives_Native.Some
                            ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                       uu____70316))
            | FStar_Syntax_Syntax.Pat_wild x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort  in
                let uu____70354 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp
                   in
                (match uu____70354 with
                 | (g1,x1,uu____70382) ->
                     let uu____70385 = ok mlty  in
                     (g1,
                       (if imp
                        then FStar_Pervasives_Native.None
                        else
                          FStar_Pervasives_Native.Some
                            ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                       uu____70385))
            | FStar_Syntax_Syntax.Pat_dot_term uu____70421 ->
                (g, FStar_Pervasives_Native.None, true)
            | FStar_Syntax_Syntax.Pat_cons (f,pats) ->
                let uu____70464 =
                  let uu____70473 = FStar_Extraction_ML_UEnv.lookup_fv g f
                     in
                  match uu____70473 with
                  | { FStar_Extraction_ML_UEnv.exp_b_name = uu____70482;
                      FStar_Extraction_ML_UEnv.exp_b_expr =
                        {
                          FStar_Extraction_ML_Syntax.expr =
                            FStar_Extraction_ML_Syntax.MLE_Name n1;
                          FStar_Extraction_ML_Syntax.mlty = uu____70484;
                          FStar_Extraction_ML_Syntax.loc = uu____70485;_};
                      FStar_Extraction_ML_UEnv.exp_b_tscheme = ttys;
                      FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____70487;_}
                      -> (n1, ttys)
                  | uu____70494 -> failwith "Expected a constructor"  in
                (match uu____70464 with
                 | (d,tys) ->
                     let nTyVars =
                       FStar_List.length (FStar_Pervasives_Native.fst tys)
                        in
                     let uu____70531 = FStar_Util.first_N nTyVars pats  in
                     (match uu____70531 with
                      | (tysVarPats,restPats) ->
                          let f_ty_opt =
                            try
                              (fun uu___1429_70635  ->
                                 match () with
                                 | () ->
                                     let mlty_args =
                                       FStar_All.pipe_right tysVarPats
                                         (FStar_List.map
                                            (fun uu____70666  ->
                                               match uu____70666 with
                                               | (p1,uu____70673) ->
                                                   (match p1.FStar_Syntax_Syntax.v
                                                    with
                                                    | FStar_Syntax_Syntax.Pat_dot_term
                                                        (uu____70676,t) ->
                                                        term_as_mlty g t
                                                    | uu____70682 ->
                                                        (FStar_Extraction_ML_UEnv.debug
                                                           g
                                                           (fun uu____70686 
                                                              ->
                                                              let uu____70687
                                                                =
                                                                FStar_Syntax_Print.pat_to_string
                                                                  p1
                                                                 in
                                                              FStar_Util.print1
                                                                "Pattern %s is not extractable"
                                                                uu____70687);
                                                         FStar_Exn.raise
                                                           Un_extractable))))
                                        in
                                     let f_ty =
                                       FStar_Extraction_ML_Util.subst tys
                                         mlty_args
                                        in
                                     let uu____70691 =
                                       FStar_Extraction_ML_Util.uncurry_mlty_fun
                                         f_ty
                                        in
                                     FStar_Pervasives_Native.Some uu____70691)
                                ()
                            with
                            | Un_extractable  -> FStar_Pervasives_Native.None
                             in
                          let uu____70720 =
                            FStar_Util.fold_map
                              (fun g1  ->
                                 fun uu____70757  ->
                                   match uu____70757 with
                                   | (p1,imp1) ->
                                       let uu____70779 =
                                         extract_one_pat true g1 p1
                                           FStar_Pervasives_Native.None
                                           term_as_mlexpr
                                          in
                                       (match uu____70779 with
                                        | (g2,p2,uu____70810) -> (g2, p2))) g
                              tysVarPats
                             in
                          (match uu____70720 with
                           | (g1,tyMLPats) ->
                               let uu____70874 =
                                 FStar_Util.fold_map
                                   (fun uu____70939  ->
                                      fun uu____70940  ->
                                        match (uu____70939, uu____70940) with
                                        | ((g2,f_ty_opt1),(p1,imp1)) ->
                                            let uu____71038 =
                                              match f_ty_opt1 with
                                              | FStar_Pervasives_Native.Some
                                                  (hd1::rest,res) ->
                                                  ((FStar_Pervasives_Native.Some
                                                      (rest, res)),
                                                    (FStar_Pervasives_Native.Some
                                                       hd1))
                                              | uu____71098 ->
                                                  (FStar_Pervasives_Native.None,
                                                    FStar_Pervasives_Native.None)
                                               in
                                            (match uu____71038 with
                                             | (f_ty_opt2,expected_ty) ->
                                                 let uu____71169 =
                                                   extract_one_pat false g2
                                                     p1 expected_ty
                                                     term_as_mlexpr
                                                    in
                                                 (match uu____71169 with
                                                  | (g3,p2,uu____71212) ->
                                                      ((g3, f_ty_opt2), p2))))
                                   (g1, f_ty_opt) restPats
                                  in
                               (match uu____70874 with
                                | ((g2,f_ty_opt1),restMLPats) ->
                                    let uu____71333 =
                                      let uu____71344 =
                                        FStar_All.pipe_right
                                          (FStar_List.append tyMLPats
                                             restMLPats)
                                          (FStar_List.collect
                                             (fun uu___618_71395  ->
                                                match uu___618_71395 with
                                                | FStar_Pervasives_Native.Some
                                                    x -> [x]
                                                | uu____71437 -> []))
                                         in
                                      FStar_All.pipe_right uu____71344
                                        FStar_List.split
                                       in
                                    (match uu____71333 with
                                     | (mlPats,when_clauses) ->
                                         let pat_ty_compat =
                                           match f_ty_opt1 with
                                           | FStar_Pervasives_Native.Some
                                               ([],t) -> ok t
                                           | uu____71513 -> false  in
                                         let uu____71523 =
                                           let uu____71532 =
                                             let uu____71539 =
                                               resugar_pat
                                                 f.FStar_Syntax_Syntax.fv_qual
                                                 (FStar_Extraction_ML_Syntax.MLP_CTor
                                                    (d, mlPats))
                                                in
                                             let uu____71542 =
                                               FStar_All.pipe_right
                                                 when_clauses
                                                 FStar_List.flatten
                                                in
                                             (uu____71539, uu____71542)  in
                                           FStar_Pervasives_Native.Some
                                             uu____71532
                                            in
                                         (g2, uu____71523, pat_ty_compat))))))
  
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
            let uu____71674 =
              extract_one_pat false g1 p1 expected_t1 term_as_mlexpr  in
            match uu____71674 with
            | (g2,FStar_Pervasives_Native.Some (x,v1),b) -> (g2, (x, v1), b)
            | uu____71737 ->
                failwith "Impossible: Unable to translate pattern"
             in
          let mk_when_clause whens =
            match whens with
            | [] -> FStar_Pervasives_Native.None
            | hd1::tl1 ->
                let uu____71785 =
                  FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd1
                    tl1
                   in
                FStar_Pervasives_Native.Some uu____71785
             in
          let uu____71786 =
            extract_one_pat1 g p (FStar_Pervasives_Native.Some expected_t)
             in
          match uu____71786 with
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
            | FStar_Extraction_ML_Syntax.MLTY_Fun (t0,uu____71946,t1) ->
                let x = FStar_Extraction_ML_Syntax.gensym ()  in
                let uu____71950 =
                  let uu____71962 =
                    let uu____71972 =
                      FStar_All.pipe_left
                        (FStar_Extraction_ML_Syntax.with_ty t0)
                        (FStar_Extraction_ML_Syntax.MLE_Var x)
                       in
                    ((x, t0), uu____71972)  in
                  uu____71962 :: more_args  in
                eta_args uu____71950 t1
            | FStar_Extraction_ML_Syntax.MLTY_Named (uu____71988,uu____71989)
                -> ((FStar_List.rev more_args), t)
            | uu____72014 ->
                let uu____72015 =
                  let uu____72017 =
                    FStar_Extraction_ML_Code.string_of_mlexpr
                      g.FStar_Extraction_ML_UEnv.currentModule mlAppExpr
                     in
                  let uu____72019 =
                    FStar_Extraction_ML_Code.string_of_mlty
                      g.FStar_Extraction_ML_UEnv.currentModule t
                     in
                  FStar_Util.format2
                    "Impossible: Head type is not an arrow: (%s : %s)"
                    uu____72017 uu____72019
                   in
                failwith uu____72015
             in
          let as_record qual1 e =
            match ((e.FStar_Extraction_ML_Syntax.expr), qual1) with
            | (FStar_Extraction_ML_Syntax.MLE_CTor
               (uu____72054,args),FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Record_ctor (tyname,fields))) ->
                let path =
                  FStar_List.map FStar_Ident.text_of_id tyname.FStar_Ident.ns
                   in
                let fields1 = record_fields fields args  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     e.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_Record (path, fields1))
            | uu____72091 -> e  in
          let resugar_and_maybe_eta qual1 e =
            let uu____72113 = eta_args [] residualType  in
            match uu____72113 with
            | (eargs,tres) ->
                (match eargs with
                 | [] ->
                     let uu____72171 = as_record qual1 e  in
                     FStar_Extraction_ML_Util.resugar_exp uu____72171
                 | uu____72172 ->
                     let uu____72184 = FStar_List.unzip eargs  in
                     (match uu____72184 with
                      | (binders,eargs1) ->
                          (match e.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_CTor (head1,args)
                               ->
                               let body =
                                 let uu____72230 =
                                   let uu____72231 =
                                     FStar_All.pipe_left
                                       (FStar_Extraction_ML_Syntax.with_ty
                                          tres)
                                       (FStar_Extraction_ML_Syntax.MLE_CTor
                                          (head1,
                                            (FStar_List.append args eargs1)))
                                      in
                                   FStar_All.pipe_left (as_record qual1)
                                     uu____72231
                                    in
                                 FStar_All.pipe_left
                                   FStar_Extraction_ML_Util.resugar_exp
                                   uu____72230
                                  in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    e.FStar_Extraction_ML_Syntax.mlty)
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    (binders, body))
                           | uu____72241 ->
                               failwith "Impossible: Not a constructor")))
             in
          match ((mlAppExpr.FStar_Extraction_ML_Syntax.expr), qual) with
          | (uu____72245,FStar_Pervasives_Native.None ) -> mlAppExpr
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____72249;
                FStar_Extraction_ML_Syntax.loc = uu____72250;_},mle::args),FStar_Pervasives_Native.Some
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
                | uu____72273 ->
                    let uu____72276 =
                      let uu____72283 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj
                         in
                      (uu____72283, args)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____72276
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
                     FStar_Extraction_ML_Syntax.mlty = uu____72287;
                     FStar_Extraction_ML_Syntax.loc = uu____72288;_},uu____72289);
                FStar_Extraction_ML_Syntax.mlty = uu____72290;
                FStar_Extraction_ML_Syntax.loc = uu____72291;_},mle::args),FStar_Pervasives_Native.Some
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
                | uu____72318 ->
                    let uu____72321 =
                      let uu____72328 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj
                         in
                      (uu____72328, args)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____72321
                 in
              FStar_Extraction_ML_Syntax.with_ty
                mlAppExpr.FStar_Extraction_ML_Syntax.mlty e
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____72332;
                FStar_Extraction_ML_Syntax.loc = uu____72333;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____72341 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____72341
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____72345;
                FStar_Extraction_ML_Syntax.loc = uu____72346;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____72348)) ->
              let uu____72361 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____72361
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____72365;
                     FStar_Extraction_ML_Syntax.loc = uu____72366;_},uu____72367);
                FStar_Extraction_ML_Syntax.mlty = uu____72368;
                FStar_Extraction_ML_Syntax.loc = uu____72369;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____72381 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____72381
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____72385;
                     FStar_Extraction_ML_Syntax.loc = uu____72386;_},uu____72387);
                FStar_Extraction_ML_Syntax.mlty = uu____72388;
                FStar_Extraction_ML_Syntax.loc = uu____72389;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____72391)) ->
              let uu____72408 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____72408
          | (FStar_Extraction_ML_Syntax.MLE_Name
             mlp,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor
             )) ->
              let uu____72414 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____72414
          | (FStar_Extraction_ML_Syntax.MLE_Name
             mlp,FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____72418)) ->
              let uu____72427 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____72427
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____72431;
                FStar_Extraction_ML_Syntax.loc = uu____72432;_},uu____72433),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____72440 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____72440
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____72444;
                FStar_Extraction_ML_Syntax.loc = uu____72445;_},uu____72446),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____72447)) ->
              let uu____72460 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____72460
          | uu____72463 -> mlAppExpr
  
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
        | uu____72494 -> (ml_e, tag)
  
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
      let maybe_generalize uu____72555 =
        match uu____72555 with
        | { FStar_Syntax_Syntax.lbname = lbname_;
            FStar_Syntax_Syntax.lbunivs = uu____72576;
            FStar_Syntax_Syntax.lbtyp = lbtyp;
            FStar_Syntax_Syntax.lbeff = lbeff;
            FStar_Syntax_Syntax.lbdef = lbdef;
            FStar_Syntax_Syntax.lbattrs = uu____72580;
            FStar_Syntax_Syntax.lbpos = uu____72581;_} ->
            let f_e = effect_as_etag g lbeff  in
            let lbtyp1 = FStar_Syntax_Subst.compress lbtyp  in
            let no_gen uu____72662 =
              let expected_t = term_as_mlty g lbtyp1  in
              (lbname_, f_e, (lbtyp1, ([], ([], expected_t))), false, lbdef)
               in
            let uu____72739 =
              FStar_TypeChecker_Util.must_erase_for_extraction
                g.FStar_Extraction_ML_UEnv.env_tcenv lbtyp1
               in
            if uu____72739
            then
              (lbname_, f_e,
                (lbtyp1, ([], ([], FStar_Extraction_ML_Syntax.MLTY_Erased))),
                false, lbdef)
            else
              (match lbtyp1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                   let uu____72825 = FStar_List.hd bs  in
                   FStar_All.pipe_right uu____72825 (is_type_binder g) ->
                   let uu____72847 = FStar_Syntax_Subst.open_comp bs c  in
                   (match uu____72847 with
                    | (bs1,c1) ->
                        let uu____72873 =
                          let uu____72886 =
                            FStar_Util.prefix_until
                              (fun x  ->
                                 let uu____72932 = is_type_binder g x  in
                                 Prims.op_Negation uu____72932) bs1
                             in
                          match uu____72886 with
                          | FStar_Pervasives_Native.None  ->
                              (bs1, (FStar_Syntax_Util.comp_result c1))
                          | FStar_Pervasives_Native.Some (bs2,b,rest) ->
                              let uu____73059 =
                                FStar_Syntax_Util.arrow (b :: rest) c1  in
                              (bs2, uu____73059)
                           in
                        (match uu____72873 with
                         | (tbinders,tbody) ->
                             let n_tbinders = FStar_List.length tbinders  in
                             let lbdef1 =
                               let uu____73121 = normalize_abs lbdef  in
                               FStar_All.pipe_right uu____73121
                                 FStar_Syntax_Util.unmeta
                                in
                             (match lbdef1.FStar_Syntax_Syntax.n with
                              | FStar_Syntax_Syntax.Tm_abs (bs2,body,copt) ->
                                  let uu____73170 =
                                    FStar_Syntax_Subst.open_term bs2 body  in
                                  (match uu____73170 with
                                   | (bs3,body1) ->
                                       if
                                         n_tbinders <=
                                           (FStar_List.length bs3)
                                       then
                                         let uu____73222 =
                                           FStar_Util.first_N n_tbinders bs3
                                            in
                                         (match uu____73222 with
                                          | (targs,rest_args) ->
                                              let expected_source_ty =
                                                let s =
                                                  FStar_List.map2
                                                    (fun uu____73325  ->
                                                       fun uu____73326  ->
                                                         match (uu____73325,
                                                                 uu____73326)
                                                         with
                                                         | ((x,uu____73352),
                                                            (y,uu____73354))
                                                             ->
                                                             let uu____73375
                                                               =
                                                               let uu____73382
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   y
                                                                  in
                                                               (x,
                                                                 uu____73382)
                                                                in
                                                             FStar_Syntax_Syntax.NT
                                                               uu____73375)
                                                    tbinders targs
                                                   in
                                                FStar_Syntax_Subst.subst s
                                                  tbody
                                                 in
                                              let env =
                                                FStar_List.fold_left
                                                  (fun env  ->
                                                     fun uu____73399  ->
                                                       match uu____73399 with
                                                       | (a,uu____73407) ->
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
                                                let uu____73418 =
                                                  FStar_All.pipe_right targs
                                                    (FStar_List.map
                                                       (fun uu____73437  ->
                                                          match uu____73437
                                                          with
                                                          | (x,uu____73446)
                                                              ->
                                                              FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                                x))
                                                   in
                                                (uu____73418, expected_t)  in
                                              let add_unit =
                                                match rest_args with
                                                | [] ->
                                                    (let uu____73462 =
                                                       is_fstar_value body1
                                                        in
                                                     Prims.op_Negation
                                                       uu____73462)
                                                      ||
                                                      (let uu____73465 =
                                                         FStar_Syntax_Util.is_pure_comp
                                                           c1
                                                          in
                                                       Prims.op_Negation
                                                         uu____73465)
                                                | uu____73467 -> false  in
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
                              | FStar_Syntax_Syntax.Tm_uinst uu____73529 ->
                                  let env =
                                    FStar_List.fold_left
                                      (fun env  ->
                                         fun uu____73548  ->
                                           match uu____73548 with
                                           | (a,uu____73556) ->
                                               FStar_Extraction_ML_UEnv.extend_ty
                                                 env a
                                                 FStar_Pervasives_Native.None)
                                      g tbinders
                                     in
                                  let expected_t = term_as_mlty env tbody  in
                                  let polytype =
                                    let uu____73567 =
                                      FStar_All.pipe_right tbinders
                                        (FStar_List.map
                                           (fun uu____73586  ->
                                              match uu____73586 with
                                              | (x,uu____73595) ->
                                                  FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                    x))
                                       in
                                    (uu____73567, expected_t)  in
                                  let args =
                                    FStar_All.pipe_right tbinders
                                      (FStar_List.map
                                         (fun uu____73639  ->
                                            match uu____73639 with
                                            | (bv,uu____73647) ->
                                                let uu____73652 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    bv
                                                   in
                                                FStar_All.pipe_right
                                                  uu____73652
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
                              | FStar_Syntax_Syntax.Tm_fvar uu____73682 ->
                                  let env =
                                    FStar_List.fold_left
                                      (fun env  ->
                                         fun uu____73695  ->
                                           match uu____73695 with
                                           | (a,uu____73703) ->
                                               FStar_Extraction_ML_UEnv.extend_ty
                                                 env a
                                                 FStar_Pervasives_Native.None)
                                      g tbinders
                                     in
                                  let expected_t = term_as_mlty env tbody  in
                                  let polytype =
                                    let uu____73714 =
                                      FStar_All.pipe_right tbinders
                                        (FStar_List.map
                                           (fun uu____73733  ->
                                              match uu____73733 with
                                              | (x,uu____73742) ->
                                                  FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                    x))
                                       in
                                    (uu____73714, expected_t)  in
                                  let args =
                                    FStar_All.pipe_right tbinders
                                      (FStar_List.map
                                         (fun uu____73786  ->
                                            match uu____73786 with
                                            | (bv,uu____73794) ->
                                                let uu____73799 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    bv
                                                   in
                                                FStar_All.pipe_right
                                                  uu____73799
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
                              | FStar_Syntax_Syntax.Tm_name uu____73829 ->
                                  let env =
                                    FStar_List.fold_left
                                      (fun env  ->
                                         fun uu____73842  ->
                                           match uu____73842 with
                                           | (a,uu____73850) ->
                                               FStar_Extraction_ML_UEnv.extend_ty
                                                 env a
                                                 FStar_Pervasives_Native.None)
                                      g tbinders
                                     in
                                  let expected_t = term_as_mlty env tbody  in
                                  let polytype =
                                    let uu____73861 =
                                      FStar_All.pipe_right tbinders
                                        (FStar_List.map
                                           (fun uu____73880  ->
                                              match uu____73880 with
                                              | (x,uu____73889) ->
                                                  FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                    x))
                                       in
                                    (uu____73861, expected_t)  in
                                  let args =
                                    FStar_All.pipe_right tbinders
                                      (FStar_List.map
                                         (fun uu____73933  ->
                                            match uu____73933 with
                                            | (bv,uu____73941) ->
                                                let uu____73946 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    bv
                                                   in
                                                FStar_All.pipe_right
                                                  uu____73946
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
                              | uu____73976 -> err_value_restriction lbdef1)))
               | uu____73996 -> no_gen ())
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
           fun uu____74147  ->
             match uu____74147 with
             | (lbname,e_tag,(typ,(binders,mltyscheme)),add_unit,_body) ->
                 let uu____74208 =
                   FStar_Extraction_ML_UEnv.extend_lb env lbname typ
                     mltyscheme add_unit is_rec
                    in
                 (match uu____74208 with
                  | (env1,uu____74225,exp_binding) ->
                      let uu____74229 =
                        let uu____74234 = FStar_Util.right lbname  in
                        (uu____74234, exp_binding)  in
                      (env1, uu____74229))) g lbs1
  
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
            (fun uu____74300  ->
               let uu____74301 = FStar_Syntax_Print.term_to_string e  in
               let uu____74303 =
                 FStar_Extraction_ML_Code.string_of_mlty
                   g.FStar_Extraction_ML_UEnv.currentModule ty
                  in
               FStar_Util.print2 "Checking %s at type %s\n" uu____74301
                 uu____74303);
          (match (f, ty) with
           | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____74310) ->
               (FStar_Extraction_ML_Syntax.ml_unit,
                 FStar_Extraction_ML_Syntax.MLTY_Erased)
           | (FStar_Extraction_ML_Syntax.E_PURE
              ,FStar_Extraction_ML_Syntax.MLTY_Erased ) ->
               (FStar_Extraction_ML_Syntax.ml_unit,
                 FStar_Extraction_ML_Syntax.MLTY_Erased)
           | uu____74311 ->
               let uu____74316 = term_as_mlexpr g e  in
               (match uu____74316 with
                | (ml_e,tag,t) ->
                    let uu____74330 = maybe_promote_effect ml_e tag t  in
                    (match uu____74330 with
                     | (ml_e1,tag1) ->
                         let uu____74341 =
                           FStar_Extraction_ML_Util.eff_leq tag1 f  in
                         if uu____74341
                         then
                           let uu____74348 =
                             maybe_coerce e.FStar_Syntax_Syntax.pos g ml_e1 t
                               ty
                              in
                           (uu____74348, ty)
                         else
                           (match (tag1, f, ty) with
                            | (FStar_Extraction_ML_Syntax.E_GHOST
                               ,FStar_Extraction_ML_Syntax.E_PURE
                               ,FStar_Extraction_ML_Syntax.MLTY_Erased ) ->
                                let uu____74355 =
                                  maybe_coerce e.FStar_Syntax_Syntax.pos g
                                    ml_e1 t ty
                                   in
                                (uu____74355, ty)
                            | uu____74356 ->
                                (err_unexpected_eff g e ty f tag1;
                                 (let uu____74364 =
                                    maybe_coerce e.FStar_Syntax_Syntax.pos g
                                      ml_e1 t ty
                                     in
                                  (uu____74364, ty)))))))

and (term_as_mlexpr :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag *
        FStar_Extraction_ML_Syntax.mlty))
  =
  fun g  ->
    fun e  ->
      let uu____74367 = term_as_mlexpr' g e  in
      match uu____74367 with
      | (e1,f,t) ->
          let uu____74383 = maybe_promote_effect e1 f t  in
          (match uu____74383 with | (e2,f1) -> (e2, f1, t))

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
           let uu____74408 =
             let uu____74410 =
               FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos  in
             let uu____74412 = FStar_Syntax_Print.tag_of_term top  in
             let uu____74414 = FStar_Syntax_Print.term_to_string top  in
             FStar_Util.format3 "%s: term_as_mlexpr' (%s) :  %s \n"
               uu____74410 uu____74412 uu____74414
              in
           FStar_Util.print_string uu____74408);
      (let t = FStar_Syntax_Subst.compress top  in
       match t.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____74424 =
             let uu____74426 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____74426
              in
           failwith uu____74424
       | FStar_Syntax_Syntax.Tm_delayed uu____74435 ->
           let uu____74458 =
             let uu____74460 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____74460
              in
           failwith uu____74458
       | FStar_Syntax_Syntax.Tm_uvar uu____74469 ->
           let uu____74482 =
             let uu____74484 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____74484
              in
           failwith uu____74482
       | FStar_Syntax_Syntax.Tm_bvar uu____74493 ->
           let uu____74494 =
             let uu____74496 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____74496
              in
           failwith uu____74494
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____74506 = FStar_Syntax_Util.unfold_lazy i  in
           term_as_mlexpr g uu____74506
       | FStar_Syntax_Syntax.Tm_type uu____74507 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_refine uu____74508 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_arrow uu____74515 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_quoted
           (qt,{
                 FStar_Syntax_Syntax.qkind =
                   FStar_Syntax_Syntax.Quote_dynamic ;
                 FStar_Syntax_Syntax.antiquotes = uu____74531;_})
           ->
           let uu____74544 =
             let uu____74545 =
               FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.failwith_lid
                 FStar_Syntax_Syntax.delta_constant
                 FStar_Pervasives_Native.None
                in
             FStar_Extraction_ML_UEnv.lookup_fv g uu____74545  in
           (match uu____74544 with
            | { FStar_Extraction_ML_UEnv.exp_b_name = uu____74552;
                FStar_Extraction_ML_UEnv.exp_b_expr = fw;
                FStar_Extraction_ML_UEnv.exp_b_tscheme = uu____74554;
                FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____74555;_} ->
                let uu____74558 =
                  let uu____74559 =
                    let uu____74560 =
                      let uu____74567 =
                        let uu____74570 =
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty
                               FStar_Extraction_ML_Syntax.ml_string_ty)
                            (FStar_Extraction_ML_Syntax.MLE_Const
                               (FStar_Extraction_ML_Syntax.MLC_String
                                  "Cannot evaluate open quotation at runtime"))
                           in
                        [uu____74570]  in
                      (fw, uu____74567)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____74560  in
                  FStar_All.pipe_left
                    (FStar_Extraction_ML_Syntax.with_ty
                       FStar_Extraction_ML_Syntax.ml_int_ty) uu____74559
                   in
                (uu____74558, FStar_Extraction_ML_Syntax.E_PURE,
                  FStar_Extraction_ML_Syntax.ml_int_ty))
       | FStar_Syntax_Syntax.Tm_quoted
           (qt,{
                 FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static ;
                 FStar_Syntax_Syntax.antiquotes = aqs;_})
           ->
           let uu____74588 = FStar_Reflection_Basic.inspect_ln qt  in
           (match uu____74588 with
            | FStar_Reflection_Data.Tv_Var bv ->
                let uu____74596 = FStar_Syntax_Syntax.lookup_aq bv aqs  in
                (match uu____74596 with
                 | FStar_Pervasives_Native.Some tm -> term_as_mlexpr g tm
                 | FStar_Pervasives_Native.None  ->
                     let tv =
                       let uu____74607 =
                         let uu____74614 =
                           FStar_Reflection_Embeddings.e_term_view_aq aqs  in
                         FStar_Syntax_Embeddings.embed uu____74614
                           (FStar_Reflection_Data.Tv_Var bv)
                          in
                       uu____74607 t.FStar_Syntax_Syntax.pos
                         FStar_Pervasives_Native.None
                         FStar_Syntax_Embeddings.id_norm_cb
                        in
                     let t1 =
                       let uu____74622 =
                         let uu____74633 = FStar_Syntax_Syntax.as_arg tv  in
                         [uu____74633]  in
                       FStar_Syntax_Util.mk_app
                         (FStar_Reflection_Data.refl_constant_term
                            FStar_Reflection_Data.fstar_refl_pack_ln)
                         uu____74622
                        in
                     term_as_mlexpr g t1)
            | tv ->
                let tv1 =
                  let uu____74660 =
                    let uu____74667 =
                      FStar_Reflection_Embeddings.e_term_view_aq aqs  in
                    FStar_Syntax_Embeddings.embed uu____74667 tv  in
                  uu____74660 t.FStar_Syntax_Syntax.pos
                    FStar_Pervasives_Native.None
                    FStar_Syntax_Embeddings.id_norm_cb
                   in
                let t1 =
                  let uu____74675 =
                    let uu____74686 = FStar_Syntax_Syntax.as_arg tv1  in
                    [uu____74686]  in
                  FStar_Syntax_Util.mk_app
                    (FStar_Reflection_Data.refl_constant_term
                       FStar_Reflection_Data.fstar_refl_pack_ln) uu____74675
                   in
                term_as_mlexpr g t1)
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_monadic (m,uu____74713)) ->
           let t2 = FStar_Syntax_Subst.compress t1  in
           (match t2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) when
                FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname ->
                let uu____74746 =
                  let uu____74753 =
                    FStar_TypeChecker_Env.effect_decl_opt
                      g.FStar_Extraction_ML_UEnv.env_tcenv m
                     in
                  FStar_Util.must uu____74753  in
                (match uu____74746 with
                 | (ed,qualifiers) ->
                     let uu____74780 =
                       let uu____74782 =
                         FStar_TypeChecker_Env.is_reifiable_effect
                           g.FStar_Extraction_ML_UEnv.env_tcenv
                           ed.FStar_Syntax_Syntax.mname
                          in
                       Prims.op_Negation uu____74782  in
                     if uu____74780
                     then term_as_mlexpr g t2
                     else
                       failwith
                         "This should not happen (should have been handled at Tm_abs level)")
            | uu____74800 -> term_as_mlexpr g t2)
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____74802) -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____74808) -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____74814 =
             FStar_TypeChecker_TcTerm.type_of_tot_term
               g.FStar_Extraction_ML_UEnv.env_tcenv t
              in
           (match uu____74814 with
            | (uu____74827,ty,uu____74829) ->
                let ml_ty = term_as_mlty g ty  in
                let uu____74831 =
                  let uu____74832 =
                    FStar_Extraction_ML_Util.mlexpr_of_const
                      t.FStar_Syntax_Syntax.pos c
                     in
                  FStar_Extraction_ML_Syntax.with_ty ml_ty uu____74832  in
                (uu____74831, FStar_Extraction_ML_Syntax.E_PURE, ml_ty))
       | FStar_Syntax_Syntax.Tm_name uu____74833 ->
           let uu____74834 = is_type g t  in
           if uu____74834
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____74845 = FStar_Extraction_ML_UEnv.lookup_term g t  in
              match uu____74845 with
              | (FStar_Util.Inl uu____74858,uu____74859) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | (FStar_Util.Inr
                 { FStar_Extraction_ML_UEnv.exp_b_name = uu____74864;
                   FStar_Extraction_ML_UEnv.exp_b_expr = x;
                   FStar_Extraction_ML_UEnv.exp_b_tscheme = mltys;
                   FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____74867;_},qual)
                  ->
                  (match mltys with
                   | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                       ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | ([],t1) ->
                       let uu____74885 =
                         maybe_eta_data_and_project_record g qual t1 x  in
                       (uu____74885, FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | uu____74886 -> err_uninst g t mltys t))
       | FStar_Syntax_Syntax.Tm_fvar fv ->
           let uu____74894 = is_type g t  in
           if uu____74894
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____74905 = FStar_Extraction_ML_UEnv.try_lookup_fv g fv
                 in
              match uu____74905 with
              | FStar_Pervasives_Native.None  ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.MLTY_Erased)
              | FStar_Pervasives_Native.Some
                  { FStar_Extraction_ML_UEnv.exp_b_name = uu____74914;
                    FStar_Extraction_ML_UEnv.exp_b_expr = x;
                    FStar_Extraction_ML_UEnv.exp_b_tscheme = mltys;
                    FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____74917;_}
                  ->
                  (FStar_Extraction_ML_UEnv.debug g
                     (fun uu____74925  ->
                        let uu____74926 = FStar_Syntax_Print.fv_to_string fv
                           in
                        let uu____74928 =
                          FStar_Extraction_ML_Code.string_of_mlexpr
                            g.FStar_Extraction_ML_UEnv.currentModule x
                           in
                        let uu____74930 =
                          FStar_Extraction_ML_Code.string_of_mlty
                            g.FStar_Extraction_ML_UEnv.currentModule
                            (FStar_Pervasives_Native.snd mltys)
                           in
                        FStar_Util.print3 "looked up %s: got %s at %s \n"
                          uu____74926 uu____74928 uu____74930);
                   (match mltys with
                    | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                        ->
                        (FStar_Extraction_ML_Syntax.ml_unit,
                          FStar_Extraction_ML_Syntax.E_PURE, t1)
                    | ([],t1) ->
                        let uu____74943 =
                          maybe_eta_data_and_project_record g
                            fv.FStar_Syntax_Syntax.fv_qual t1 x
                           in
                        (uu____74943, FStar_Extraction_ML_Syntax.E_PURE, t1)
                    | uu____74944 -> err_uninst g t mltys t)))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,rcopt) ->
           let uu____74978 = FStar_Syntax_Subst.open_term bs body  in
           (match uu____74978 with
            | (bs1,body1) ->
                let uu____74991 = binders_as_ml_binders g bs1  in
                (match uu____74991 with
                 | (ml_bs,env) ->
                     let body2 =
                       match rcopt with
                       | FStar_Pervasives_Native.Some rc ->
                           let uu____75027 =
                             FStar_TypeChecker_Env.is_reifiable_rc
                               env.FStar_Extraction_ML_UEnv.env_tcenv rc
                              in
                           if uu____75027
                           then
                             FStar_TypeChecker_Util.reify_body
                               env.FStar_Extraction_ML_UEnv.env_tcenv body1
                           else body1
                       | FStar_Pervasives_Native.None  ->
                           (FStar_Extraction_ML_UEnv.debug g
                              (fun uu____75035  ->
                                 let uu____75036 =
                                   FStar_Syntax_Print.term_to_string body1
                                    in
                                 FStar_Util.print1
                                   "No computation type for: %s\n"
                                   uu____75036);
                            body1)
                        in
                     let uu____75039 = term_as_mlexpr env body2  in
                     (match uu____75039 with
                      | (ml_body,f,t1) ->
                          let uu____75055 =
                            FStar_List.fold_right
                              (fun uu____75075  ->
                                 fun uu____75076  ->
                                   match (uu____75075, uu____75076) with
                                   | ((uu____75099,targ),(f1,t2)) ->
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         (FStar_Extraction_ML_Syntax.MLTY_Fun
                                            (targ, f1, t2)))) ml_bs (f, t1)
                             in
                          (match uu____75055 with
                           | (f1,tfun) ->
                               let uu____75122 =
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty tfun)
                                   (FStar_Extraction_ML_Syntax.MLE_Fun
                                      (ml_bs, ml_body))
                                  in
                               (uu____75122, f1, tfun)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____75130;
              FStar_Syntax_Syntax.vars = uu____75131;_},(a1,uu____75133)::[])
           ->
           let ty =
             let uu____75173 =
               FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid  in
             term_as_mlty g uu____75173  in
           let uu____75174 =
             let uu____75175 =
               FStar_Extraction_ML_Util.mlexpr_of_range
                 a1.FStar_Syntax_Syntax.pos
                in
             FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty)
               uu____75175
              in
           (uu____75174, FStar_Extraction_ML_Syntax.E_PURE, ty)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____75176;
              FStar_Syntax_Syntax.vars = uu____75177;_},(t1,uu____75179)::
            (r,uu____75181)::[])
           -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____75236);
              FStar_Syntax_Syntax.pos = uu____75237;
              FStar_Syntax_Syntax.vars = uu____75238;_},uu____75239)
           -> failwith "Unreachable? Tm_app Const_reflect"
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let is_total rc =
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_Tot_lid)
               ||
               (FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
                  (FStar_List.existsb
                     (fun uu___619_75308  ->
                        match uu___619_75308 with
                        | FStar_Syntax_Syntax.TOTAL  -> true
                        | uu____75311 -> false)))
              in
           let uu____75313 =
             let uu____75318 =
               let uu____75319 = FStar_Syntax_Subst.compress head1  in
               uu____75319.FStar_Syntax_Syntax.n  in
             ((head1.FStar_Syntax_Syntax.n), uu____75318)  in
           (match uu____75313 with
            | (FStar_Syntax_Syntax.Tm_uvar uu____75328,uu____75329) ->
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
            | (uu____75343,FStar_Syntax_Syntax.Tm_abs
               (bs,uu____75345,FStar_Pervasives_Native.Some rc)) when
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
            | (uu____75370,FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_reify )) ->
                let e =
                  let uu____75372 = FStar_List.hd args  in
                  FStar_TypeChecker_Util.reify_body_with_arg
                    g.FStar_Extraction_ML_UEnv.env_tcenv head1 uu____75372
                   in
                let tm =
                  let uu____75384 =
                    let uu____75389 = FStar_TypeChecker_Util.remove_reify e
                       in
                    let uu____75390 = FStar_List.tl args  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____75389 uu____75390  in
                  uu____75384 FStar_Pervasives_Native.None
                    t.FStar_Syntax_Syntax.pos
                   in
                term_as_mlexpr g tm
            | uu____75399 ->
                let rec extract_app is_data uu____75452 uu____75453 restArgs
                  =
                  match (uu____75452, uu____75453) with
                  | ((mlhead,mlargs_f),(f,t1)) ->
                      let mk_head uu____75534 =
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
                         (fun uu____75561  ->
                            let uu____75562 =
                              let uu____75564 = mk_head ()  in
                              FStar_Extraction_ML_Code.string_of_mlexpr
                                g.FStar_Extraction_ML_UEnv.currentModule
                                uu____75564
                               in
                            let uu____75565 =
                              FStar_Extraction_ML_Code.string_of_mlty
                                g.FStar_Extraction_ML_UEnv.currentModule t1
                               in
                            let uu____75567 =
                              match restArgs with
                              | [] -> "none"
                              | (hd1,uu____75578)::uu____75579 ->
                                  FStar_Syntax_Print.term_to_string hd1
                               in
                            FStar_Util.print3
                              "extract_app ml_head=%s type of head = %s, next arg = %s\n"
                              uu____75562 uu____75565 uu____75567);
                       (match (restArgs, t1) with
                        | ([],uu____75613) ->
                            let app =
                              let uu____75629 = mk_head ()  in
                              maybe_eta_data_and_project_record g is_data t1
                                uu____75629
                               in
                            (app, f, t1)
                        | ((arg,uu____75631)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                           (formal_t,f',t2)) when
                            (is_type g arg) &&
                              (type_leq g formal_t
                                 FStar_Extraction_ML_Syntax.ml_unit_ty)
                            ->
                            let uu____75662 =
                              let uu____75667 =
                                FStar_Extraction_ML_Util.join
                                  arg.FStar_Syntax_Syntax.pos f f'
                                 in
                              (uu____75667, t2)  in
                            extract_app is_data
                              (mlhead,
                                ((FStar_Extraction_ML_Syntax.ml_unit,
                                   FStar_Extraction_ML_Syntax.E_PURE) ::
                                mlargs_f)) uu____75662 rest
                        | ((e0,uu____75679)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                           (tExpected,f',t2)) ->
                            let r = e0.FStar_Syntax_Syntax.pos  in
                            let expected_effect =
                              let uu____75712 =
                                (FStar_Options.lax ()) &&
                                  (FStar_TypeChecker_Util.short_circuit_head
                                     head1)
                                 in
                              if uu____75712
                              then FStar_Extraction_ML_Syntax.E_IMPURE
                              else FStar_Extraction_ML_Syntax.E_PURE  in
                            let uu____75717 =
                              check_term_as_mlexpr g e0 expected_effect
                                tExpected
                               in
                            (match uu____75717 with
                             | (e01,tInferred) ->
                                 let uu____75730 =
                                   let uu____75735 =
                                     FStar_Extraction_ML_Util.join_l r
                                       [f; f']
                                      in
                                   (uu____75735, t2)  in
                                 extract_app is_data
                                   (mlhead, ((e01, expected_effect) ::
                                     mlargs_f)) uu____75730 rest)
                        | uu____75746 ->
                            let uu____75759 =
                              FStar_Extraction_ML_Util.udelta_unfold g t1  in
                            (match uu____75759 with
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
                                  | uu____75831 ->
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
                let extract_app_maybe_projector is_data mlhead uu____75902
                  args1 =
                  match uu____75902 with
                  | (f,t1) ->
                      (match is_data with
                       | FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_projector uu____75932)
                           ->
                           let rec remove_implicits args2 f1 t2 =
                             match (args2, t2) with
                             | ((a0,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____76016))::args3,FStar_Extraction_ML_Syntax.MLTY_Fun
                                (uu____76018,f',t3)) ->
                                 let uu____76056 =
                                   FStar_Extraction_ML_Util.join
                                     a0.FStar_Syntax_Syntax.pos f1 f'
                                    in
                                 remove_implicits args3 uu____76056 t3
                             | uu____76057 -> (args2, f1, t2)  in
                           let uu____76082 = remove_implicits args1 f t1  in
                           (match uu____76082 with
                            | (args2,f1,t2) ->
                                extract_app is_data (mlhead, []) (f1, t2)
                                  args2)
                       | uu____76138 ->
                           extract_app is_data (mlhead, []) (f, t1) args1)
                   in
                let extract_app_with_instantiations uu____76162 =
                  let head2 = FStar_Syntax_Util.un_uinst head1  in
                  match head2.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_name uu____76170 ->
                      let uu____76171 =
                        let uu____76192 =
                          FStar_Extraction_ML_UEnv.lookup_term g head2  in
                        match uu____76192 with
                        | (FStar_Util.Inr exp_b,q) ->
                            (FStar_Extraction_ML_UEnv.debug g
                               (fun uu____76231  ->
                                  let uu____76232 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  let uu____76234 =
                                    FStar_Extraction_ML_Code.string_of_mlexpr
                                      g.FStar_Extraction_ML_UEnv.currentModule
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_expr
                                     in
                                  let uu____76236 =
                                    FStar_Extraction_ML_Code.string_of_mlty
                                      g.FStar_Extraction_ML_UEnv.currentModule
                                      (FStar_Pervasives_Native.snd
                                         exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme)
                                     in
                                  let uu____76238 =
                                    FStar_Util.string_of_bool
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok
                                     in
                                  FStar_Util.print4
                                    "@@@looked up %s: got %s at %s (inst_ok=%s)\n"
                                    uu____76232 uu____76234 uu____76236
                                    uu____76238);
                             (((exp_b.FStar_Extraction_ML_UEnv.exp_b_expr),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok)),
                               q))
                        | uu____76265 -> failwith "FIXME Ty"  in
                      (match uu____76171 with
                       | ((head_ml,(vars,t1),inst_ok),qual) ->
                           let has_typ_apps =
                             match args with
                             | (a,uu____76341)::uu____76342 -> is_type g a
                             | uu____76369 -> false  in
                           let uu____76381 =
                             match vars with
                             | uu____76410::uu____76411 when
                                 (Prims.op_Negation has_typ_apps) && inst_ok
                                 -> (head_ml, t1, args)
                             | uu____76425 ->
                                 let n1 = FStar_List.length vars  in
                                 if n1 <= (FStar_List.length args)
                                 then
                                   let uu____76454 =
                                     FStar_Util.first_N n1 args  in
                                   (match uu____76454 with
                                    | (prefix1,rest) ->
                                        let prefixAsMLTypes =
                                          FStar_List.map
                                            (fun uu____76555  ->
                                               match uu____76555 with
                                               | (x,uu____76563) ->
                                                   term_as_mlty g x) prefix1
                                           in
                                        let t2 =
                                          instantiate (vars, t1)
                                            prefixAsMLTypes
                                           in
                                        (FStar_Extraction_ML_UEnv.debug g
                                           (fun uu____76575  ->
                                              let uu____76576 =
                                                FStar_Syntax_Print.term_to_string
                                                  head2
                                                 in
                                              let uu____76578 =
                                                FStar_Syntax_Print.args_to_string
                                                  prefix1
                                                 in
                                              let uu____76580 =
                                                let uu____76582 =
                                                  FStar_List.map
                                                    (FStar_Extraction_ML_Code.string_of_mlty
                                                       g.FStar_Extraction_ML_UEnv.currentModule)
                                                    prefixAsMLTypes
                                                   in
                                                FStar_All.pipe_right
                                                  uu____76582
                                                  (FStar_String.concat ", ")
                                                 in
                                              let uu____76592 =
                                                FStar_Extraction_ML_Code.string_of_mlty
                                                  g.FStar_Extraction_ML_UEnv.currentModule
                                                  t2
                                                 in
                                              FStar_Util.print4
                                                "@@@looked up %s, instantiated with [%s] translated to [%s], got %s\n"
                                                uu____76576 uu____76578
                                                uu____76580 uu____76592);
                                         (let mk_tapp e ty_args =
                                            match ty_args with
                                            | [] -> e
                                            | uu____76610 ->
                                                let uu___2234_76613 = e  in
                                                {
                                                  FStar_Extraction_ML_Syntax.expr
                                                    =
                                                    (FStar_Extraction_ML_Syntax.MLE_TApp
                                                       (e, ty_args));
                                                  FStar_Extraction_ML_Syntax.mlty
                                                    =
                                                    (uu___2234_76613.FStar_Extraction_ML_Syntax.mlty);
                                                  FStar_Extraction_ML_Syntax.loc
                                                    =
                                                    (uu___2234_76613.FStar_Extraction_ML_Syntax.loc)
                                                }
                                             in
                                          let head3 =
                                            match head_ml.FStar_Extraction_ML_Syntax.expr
                                            with
                                            | FStar_Extraction_ML_Syntax.MLE_Name
                                                uu____76617 ->
                                                let uu___2240_76618 =
                                                  mk_tapp head_ml
                                                    prefixAsMLTypes
                                                   in
                                                {
                                                  FStar_Extraction_ML_Syntax.expr
                                                    =
                                                    (uu___2240_76618.FStar_Extraction_ML_Syntax.expr);
                                                  FStar_Extraction_ML_Syntax.mlty
                                                    = t2;
                                                  FStar_Extraction_ML_Syntax.loc
                                                    =
                                                    (uu___2240_76618.FStar_Extraction_ML_Syntax.loc)
                                                }
                                            | FStar_Extraction_ML_Syntax.MLE_Var
                                                uu____76619 ->
                                                let uu___2240_76621 =
                                                  mk_tapp head_ml
                                                    prefixAsMLTypes
                                                   in
                                                {
                                                  FStar_Extraction_ML_Syntax.expr
                                                    =
                                                    (uu___2240_76621.FStar_Extraction_ML_Syntax.expr);
                                                  FStar_Extraction_ML_Syntax.mlty
                                                    = t2;
                                                  FStar_Extraction_ML_Syntax.loc
                                                    =
                                                    (uu___2240_76621.FStar_Extraction_ML_Syntax.loc)
                                                }
                                            | FStar_Extraction_ML_Syntax.MLE_App
                                                (head3,{
                                                         FStar_Extraction_ML_Syntax.expr
                                                           =
                                                           FStar_Extraction_ML_Syntax.MLE_Const
                                                           (FStar_Extraction_ML_Syntax.MLC_Unit
                                                           );
                                                         FStar_Extraction_ML_Syntax.mlty
                                                           = uu____76623;
                                                         FStar_Extraction_ML_Syntax.loc
                                                           = uu____76624;_}::[])
                                                ->
                                                FStar_All.pipe_right
                                                  (FStar_Extraction_ML_Syntax.MLE_App
                                                     ((let uu___2251_76630 =
                                                         mk_tapp head3
                                                           prefixAsMLTypes
                                                          in
                                                       {
                                                         FStar_Extraction_ML_Syntax.expr
                                                           =
                                                           (uu___2251_76630.FStar_Extraction_ML_Syntax.expr);
                                                         FStar_Extraction_ML_Syntax.mlty
                                                           =
                                                           (FStar_Extraction_ML_Syntax.MLTY_Fun
                                                              (FStar_Extraction_ML_Syntax.ml_unit_ty,
                                                                FStar_Extraction_ML_Syntax.E_PURE,
                                                                t2));
                                                         FStar_Extraction_ML_Syntax.loc
                                                           =
                                                           (uu___2251_76630.FStar_Extraction_ML_Syntax.loc)
                                                       }),
                                                       [FStar_Extraction_ML_Syntax.ml_unit]))
                                                  (FStar_Extraction_ML_Syntax.with_ty
                                                     t2)
                                            | uu____76631 ->
                                                failwith
                                                  "Impossible: Unexpected head term"
                                             in
                                          (head3, t2, rest))))
                                 else err_uninst g head2 (vars, t1) top
                              in
                           (match uu____76381 with
                            | (head_ml1,head_t,args1) ->
                                (match args1 with
                                 | [] ->
                                     let uu____76697 =
                                       maybe_eta_data_and_project_record g
                                         qual head_t head_ml1
                                        in
                                     (uu____76697,
                                       FStar_Extraction_ML_Syntax.E_PURE,
                                       head_t)
                                 | uu____76698 ->
                                     extract_app_maybe_projector qual
                                       head_ml1
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         head_t) args1)))
                  | FStar_Syntax_Syntax.Tm_fvar uu____76707 ->
                      let uu____76708 =
                        let uu____76729 =
                          FStar_Extraction_ML_UEnv.lookup_term g head2  in
                        match uu____76729 with
                        | (FStar_Util.Inr exp_b,q) ->
                            (FStar_Extraction_ML_UEnv.debug g
                               (fun uu____76768  ->
                                  let uu____76769 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  let uu____76771 =
                                    FStar_Extraction_ML_Code.string_of_mlexpr
                                      g.FStar_Extraction_ML_UEnv.currentModule
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_expr
                                     in
                                  let uu____76773 =
                                    FStar_Extraction_ML_Code.string_of_mlty
                                      g.FStar_Extraction_ML_UEnv.currentModule
                                      (FStar_Pervasives_Native.snd
                                         exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme)
                                     in
                                  let uu____76775 =
                                    FStar_Util.string_of_bool
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok
                                     in
                                  FStar_Util.print4
                                    "@@@looked up %s: got %s at %s (inst_ok=%s)\n"
                                    uu____76769 uu____76771 uu____76773
                                    uu____76775);
                             (((exp_b.FStar_Extraction_ML_UEnv.exp_b_expr),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok)),
                               q))
                        | uu____76802 -> failwith "FIXME Ty"  in
                      (match uu____76708 with
                       | ((head_ml,(vars,t1),inst_ok),qual) ->
                           let has_typ_apps =
                             match args with
                             | (a,uu____76878)::uu____76879 -> is_type g a
                             | uu____76906 -> false  in
                           let uu____76918 =
                             match vars with
                             | uu____76947::uu____76948 when
                                 (Prims.op_Negation has_typ_apps) && inst_ok
                                 -> (head_ml, t1, args)
                             | uu____76962 ->
                                 let n1 = FStar_List.length vars  in
                                 if n1 <= (FStar_List.length args)
                                 then
                                   let uu____76991 =
                                     FStar_Util.first_N n1 args  in
                                   (match uu____76991 with
                                    | (prefix1,rest) ->
                                        let prefixAsMLTypes =
                                          FStar_List.map
                                            (fun uu____77092  ->
                                               match uu____77092 with
                                               | (x,uu____77100) ->
                                                   term_as_mlty g x) prefix1
                                           in
                                        let t2 =
                                          instantiate (vars, t1)
                                            prefixAsMLTypes
                                           in
                                        (FStar_Extraction_ML_UEnv.debug g
                                           (fun uu____77112  ->
                                              let uu____77113 =
                                                FStar_Syntax_Print.term_to_string
                                                  head2
                                                 in
                                              let uu____77115 =
                                                FStar_Syntax_Print.args_to_string
                                                  prefix1
                                                 in
                                              let uu____77117 =
                                                let uu____77119 =
                                                  FStar_List.map
                                                    (FStar_Extraction_ML_Code.string_of_mlty
                                                       g.FStar_Extraction_ML_UEnv.currentModule)
                                                    prefixAsMLTypes
                                                   in
                                                FStar_All.pipe_right
                                                  uu____77119
                                                  (FStar_String.concat ", ")
                                                 in
                                              let uu____77129 =
                                                FStar_Extraction_ML_Code.string_of_mlty
                                                  g.FStar_Extraction_ML_UEnv.currentModule
                                                  t2
                                                 in
                                              FStar_Util.print4
                                                "@@@looked up %s, instantiated with [%s] translated to [%s], got %s\n"
                                                uu____77113 uu____77115
                                                uu____77117 uu____77129);
                                         (let mk_tapp e ty_args =
                                            match ty_args with
                                            | [] -> e
                                            | uu____77147 ->
                                                let uu___2234_77150 = e  in
                                                {
                                                  FStar_Extraction_ML_Syntax.expr
                                                    =
                                                    (FStar_Extraction_ML_Syntax.MLE_TApp
                                                       (e, ty_args));
                                                  FStar_Extraction_ML_Syntax.mlty
                                                    =
                                                    (uu___2234_77150.FStar_Extraction_ML_Syntax.mlty);
                                                  FStar_Extraction_ML_Syntax.loc
                                                    =
                                                    (uu___2234_77150.FStar_Extraction_ML_Syntax.loc)
                                                }
                                             in
                                          let head3 =
                                            match head_ml.FStar_Extraction_ML_Syntax.expr
                                            with
                                            | FStar_Extraction_ML_Syntax.MLE_Name
                                                uu____77154 ->
                                                let uu___2240_77155 =
                                                  mk_tapp head_ml
                                                    prefixAsMLTypes
                                                   in
                                                {
                                                  FStar_Extraction_ML_Syntax.expr
                                                    =
                                                    (uu___2240_77155.FStar_Extraction_ML_Syntax.expr);
                                                  FStar_Extraction_ML_Syntax.mlty
                                                    = t2;
                                                  FStar_Extraction_ML_Syntax.loc
                                                    =
                                                    (uu___2240_77155.FStar_Extraction_ML_Syntax.loc)
                                                }
                                            | FStar_Extraction_ML_Syntax.MLE_Var
                                                uu____77156 ->
                                                let uu___2240_77158 =
                                                  mk_tapp head_ml
                                                    prefixAsMLTypes
                                                   in
                                                {
                                                  FStar_Extraction_ML_Syntax.expr
                                                    =
                                                    (uu___2240_77158.FStar_Extraction_ML_Syntax.expr);
                                                  FStar_Extraction_ML_Syntax.mlty
                                                    = t2;
                                                  FStar_Extraction_ML_Syntax.loc
                                                    =
                                                    (uu___2240_77158.FStar_Extraction_ML_Syntax.loc)
                                                }
                                            | FStar_Extraction_ML_Syntax.MLE_App
                                                (head3,{
                                                         FStar_Extraction_ML_Syntax.expr
                                                           =
                                                           FStar_Extraction_ML_Syntax.MLE_Const
                                                           (FStar_Extraction_ML_Syntax.MLC_Unit
                                                           );
                                                         FStar_Extraction_ML_Syntax.mlty
                                                           = uu____77160;
                                                         FStar_Extraction_ML_Syntax.loc
                                                           = uu____77161;_}::[])
                                                ->
                                                FStar_All.pipe_right
                                                  (FStar_Extraction_ML_Syntax.MLE_App
                                                     ((let uu___2251_77167 =
                                                         mk_tapp head3
                                                           prefixAsMLTypes
                                                          in
                                                       {
                                                         FStar_Extraction_ML_Syntax.expr
                                                           =
                                                           (uu___2251_77167.FStar_Extraction_ML_Syntax.expr);
                                                         FStar_Extraction_ML_Syntax.mlty
                                                           =
                                                           (FStar_Extraction_ML_Syntax.MLTY_Fun
                                                              (FStar_Extraction_ML_Syntax.ml_unit_ty,
                                                                FStar_Extraction_ML_Syntax.E_PURE,
                                                                t2));
                                                         FStar_Extraction_ML_Syntax.loc
                                                           =
                                                           (uu___2251_77167.FStar_Extraction_ML_Syntax.loc)
                                                       }),
                                                       [FStar_Extraction_ML_Syntax.ml_unit]))
                                                  (FStar_Extraction_ML_Syntax.with_ty
                                                     t2)
                                            | uu____77168 ->
                                                failwith
                                                  "Impossible: Unexpected head term"
                                             in
                                          (head3, t2, rest))))
                                 else err_uninst g head2 (vars, t1) top
                              in
                           (match uu____76918 with
                            | (head_ml1,head_t,args1) ->
                                (match args1 with
                                 | [] ->
                                     let uu____77234 =
                                       maybe_eta_data_and_project_record g
                                         qual head_t head_ml1
                                        in
                                     (uu____77234,
                                       FStar_Extraction_ML_Syntax.E_PURE,
                                       head_t)
                                 | uu____77235 ->
                                     extract_app_maybe_projector qual
                                       head_ml1
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         head_t) args1)))
                  | uu____77244 ->
                      let uu____77245 = term_as_mlexpr g head2  in
                      (match uu____77245 with
                       | (head3,f,t1) ->
                           extract_app_maybe_projector
                             FStar_Pervasives_Native.None head3 (f, t1) args)
                   in
                let uu____77261 = is_type g t  in
                if uu____77261
                then
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
                else
                  (let uu____77272 =
                     let uu____77273 = FStar_Syntax_Util.un_uinst head1  in
                     uu____77273.FStar_Syntax_Syntax.n  in
                   match uu____77272 with
                   | FStar_Syntax_Syntax.Tm_fvar fv ->
                       let uu____77283 =
                         FStar_Extraction_ML_UEnv.try_lookup_fv g fv  in
                       (match uu____77283 with
                        | FStar_Pervasives_Native.None  ->
                            (FStar_Extraction_ML_Syntax.ml_unit,
                              FStar_Extraction_ML_Syntax.E_PURE,
                              FStar_Extraction_ML_Syntax.MLTY_Erased)
                        | uu____77292 -> extract_app_with_instantiations ())
                   | uu____77295 -> extract_app_with_instantiations ()))
       | FStar_Syntax_Syntax.Tm_ascribed (e0,(tc,uu____77298),f) ->
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
           let uu____77366 = check_term_as_mlexpr g e0 f1 t1  in
           (match uu____77366 with | (e,t2) -> (e, f1, t2))
       | FStar_Syntax_Syntax.Tm_let ((is_rec,lbs),e') ->
           let top_level = FStar_Syntax_Syntax.is_top_level lbs  in
           let uu____77401 =
             if is_rec
             then FStar_Syntax_Subst.open_let_rec lbs e'
             else
               (let uu____77417 = FStar_Syntax_Syntax.is_top_level lbs  in
                if uu____77417
                then (lbs, e')
                else
                  (let lb = FStar_List.hd lbs  in
                   let x =
                     let uu____77432 =
                       FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                     FStar_Syntax_Syntax.freshen_bv uu____77432  in
                   let lb1 =
                     let uu___2302_77434 = lb  in
                     {
                       FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                       FStar_Syntax_Syntax.lbunivs =
                         (uu___2302_77434.FStar_Syntax_Syntax.lbunivs);
                       FStar_Syntax_Syntax.lbtyp =
                         (uu___2302_77434.FStar_Syntax_Syntax.lbtyp);
                       FStar_Syntax_Syntax.lbeff =
                         (uu___2302_77434.FStar_Syntax_Syntax.lbeff);
                       FStar_Syntax_Syntax.lbdef =
                         (uu___2302_77434.FStar_Syntax_Syntax.lbdef);
                       FStar_Syntax_Syntax.lbattrs =
                         (uu___2302_77434.FStar_Syntax_Syntax.lbattrs);
                       FStar_Syntax_Syntax.lbpos =
                         (uu___2302_77434.FStar_Syntax_Syntax.lbpos)
                     }  in
                   let e'1 =
                     FStar_Syntax_Subst.subst
                       [FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x)] e'
                      in
                   ([lb1], e'1)))
              in
           (match uu____77401 with
            | (lbs1,e'1) ->
                let lbs2 =
                  if top_level
                  then
                    FStar_All.pipe_right lbs1
                      (FStar_List.map
                         (fun lb  ->
                            let tcenv =
                              let uu____77468 =
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
                                uu____77468
                               in
                            let lbdef =
                              let uu____77483 = FStar_Options.ml_ish ()  in
                              if uu____77483
                              then lb.FStar_Syntax_Syntax.lbdef
                              else
                                (let norm_call uu____77495 =
                                   FStar_TypeChecker_Normalize.normalize
                                     (FStar_TypeChecker_Env.PureSubtermsWithinComputations
                                     :: extraction_norm_steps) tcenv
                                     lb.FStar_Syntax_Syntax.lbdef
                                    in
                                 let uu____77496 =
                                   (FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug tcenv)
                                      (FStar_Options.Other "Extraction"))
                                     ||
                                     (FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug tcenv)
                                        (FStar_Options.Other "ExtractNorm"))
                                    in
                                 if uu____77496
                                 then
                                   ((let uu____77506 =
                                       FStar_Syntax_Print.lbname_to_string
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     let uu____77508 =
                                       FStar_Syntax_Print.term_to_string
                                         lb.FStar_Syntax_Syntax.lbdef
                                        in
                                     FStar_Util.print2
                                       "Starting to normalize top-level let %s)\n\tlbdef=%s"
                                       uu____77506 uu____77508);
                                    (let a =
                                       let uu____77514 =
                                         let uu____77516 =
                                           FStar_Syntax_Print.lbname_to_string
                                             lb.FStar_Syntax_Syntax.lbname
                                            in
                                         FStar_Util.format1
                                           "###(Time to normalize top-level let %s)"
                                           uu____77516
                                          in
                                       FStar_Util.measure_execution_time
                                         uu____77514 norm_call
                                        in
                                     (let uu____77522 =
                                        FStar_Syntax_Print.term_to_string a
                                         in
                                      FStar_Util.print1 "Normalized to %s\n"
                                        uu____77522);
                                     a))
                                 else norm_call ())
                               in
                            let uu___2320_77527 = lb  in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___2320_77527.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___2320_77527.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp =
                                (uu___2320_77527.FStar_Syntax_Syntax.lbtyp);
                              FStar_Syntax_Syntax.lbeff =
                                (uu___2320_77527.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = lbdef;
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___2320_77527.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___2320_77527.FStar_Syntax_Syntax.lbpos)
                            }))
                  else lbs1  in
                let check_lb env uu____77580 =
                  match uu____77580 with
                  | (nm,(_lbname,f,(_t,(targs,polytype)),add_unit,e)) ->
                      let env1 =
                        FStar_List.fold_left
                          (fun env1  ->
                             fun uu____77736  ->
                               match uu____77736 with
                               | (a,uu____77744) ->
                                   FStar_Extraction_ML_UEnv.extend_ty env1 a
                                     FStar_Pervasives_Native.None) env targs
                         in
                      let expected_t = FStar_Pervasives_Native.snd polytype
                         in
                      let uu____77750 =
                        check_term_as_mlexpr env1 e f expected_t  in
                      (match uu____77750 with
                       | (e1,ty) ->
                           let uu____77761 =
                             maybe_promote_effect e1 f expected_t  in
                           (match uu____77761 with
                            | (e2,f1) ->
                                let meta =
                                  match (f1, ty) with
                                  | (FStar_Extraction_ML_Syntax.E_PURE
                                     ,FStar_Extraction_ML_Syntax.MLTY_Erased
                                     ) -> [FStar_Extraction_ML_Syntax.Erased]
                                  | (FStar_Extraction_ML_Syntax.E_GHOST
                                     ,FStar_Extraction_ML_Syntax.MLTY_Erased
                                     ) -> [FStar_Extraction_ML_Syntax.Erased]
                                  | uu____77773 -> []  in
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
                let uu____77804 =
                  FStar_List.fold_right
                    (fun lb  ->
                       fun uu____77901  ->
                         match uu____77901 with
                         | (env,lbs4) ->
                             let uu____78035 = lb  in
                             (match uu____78035 with
                              | (lbname,uu____78086,(t1,(uu____78088,polytype)),add_unit,uu____78091)
                                  ->
                                  let uu____78106 =
                                    FStar_Extraction_ML_UEnv.extend_lb env
                                      lbname t1 polytype add_unit true
                                     in
                                  (match uu____78106 with
                                   | (env1,nm,uu____78147) ->
                                       (env1, ((nm, lb) :: lbs4))))) lbs3
                    (g, [])
                   in
                (match uu____77804 with
                 | (env_body,lbs4) ->
                     let env_def = if is_rec then env_body else g  in
                     let lbs5 =
                       FStar_All.pipe_right lbs4
                         (FStar_List.map (check_lb env_def))
                        in
                     let e'_rng = e'1.FStar_Syntax_Syntax.pos  in
                     let uu____78426 = term_as_mlexpr env_body e'1  in
                     (match uu____78426 with
                      | (e'2,f',t') ->
                          let f =
                            let uu____78443 =
                              let uu____78446 =
                                FStar_List.map FStar_Pervasives_Native.fst
                                  lbs5
                                 in
                              f' :: uu____78446  in
                            FStar_Extraction_ML_Util.join_l e'_rng
                              uu____78443
                             in
                          let is_rec1 =
                            if is_rec = true
                            then FStar_Extraction_ML_Syntax.Rec
                            else FStar_Extraction_ML_Syntax.NonRec  in
                          let uu____78459 =
                            let uu____78460 =
                              let uu____78461 =
                                let uu____78462 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    lbs5
                                   in
                                (is_rec1, uu____78462)  in
                              mk_MLE_Let top_level uu____78461 e'2  in
                            let uu____78471 =
                              FStar_Extraction_ML_Util.mlloc_of_range
                                t.FStar_Syntax_Syntax.pos
                               in
                            FStar_Extraction_ML_Syntax.with_ty_loc t'
                              uu____78460 uu____78471
                             in
                          (uu____78459, f, t'))))
       | FStar_Syntax_Syntax.Tm_match (scrutinee,pats) ->
           let uu____78510 = term_as_mlexpr g scrutinee  in
           (match uu____78510 with
            | (e,f_e,t_e) ->
                let uu____78526 = check_pats_for_ite pats  in
                (match uu____78526 with
                 | (b,then_e,else_e) ->
                     let no_lift x t1 = x  in
                     if b
                     then
                       (match (then_e, else_e) with
                        | (FStar_Pervasives_Native.Some
                           then_e1,FStar_Pervasives_Native.Some else_e1) ->
                            let uu____78591 = term_as_mlexpr g then_e1  in
                            (match uu____78591 with
                             | (then_mle,f_then,t_then) ->
                                 let uu____78607 = term_as_mlexpr g else_e1
                                    in
                                 (match uu____78607 with
                                  | (else_mle,f_else,t_else) ->
                                      let uu____78623 =
                                        let uu____78634 =
                                          type_leq g t_then t_else  in
                                        if uu____78634
                                        then (t_else, no_lift)
                                        else
                                          (let uu____78655 =
                                             type_leq g t_else t_then  in
                                           if uu____78655
                                           then (t_then, no_lift)
                                           else
                                             (FStar_Extraction_ML_Syntax.MLTY_Top,
                                               FStar_Extraction_ML_Syntax.apply_obj_repr))
                                         in
                                      (match uu____78623 with
                                       | (t_branch,maybe_lift1) ->
                                           let uu____78702 =
                                             let uu____78703 =
                                               let uu____78704 =
                                                 let uu____78713 =
                                                   maybe_lift1 then_mle
                                                     t_then
                                                    in
                                                 let uu____78714 =
                                                   let uu____78717 =
                                                     maybe_lift1 else_mle
                                                       t_else
                                                      in
                                                   FStar_Pervasives_Native.Some
                                                     uu____78717
                                                    in
                                                 (e, uu____78713,
                                                   uu____78714)
                                                  in
                                               FStar_Extraction_ML_Syntax.MLE_If
                                                 uu____78704
                                                in
                                             FStar_All.pipe_left
                                               (FStar_Extraction_ML_Syntax.with_ty
                                                  t_branch) uu____78703
                                              in
                                           let uu____78720 =
                                             FStar_Extraction_ML_Util.join
                                               then_e1.FStar_Syntax_Syntax.pos
                                               f_then f_else
                                              in
                                           (uu____78702, uu____78720,
                                             t_branch))))
                        | uu____78721 ->
                            failwith
                              "ITE pats matched but then and else expressions not found?")
                     else
                       (let uu____78739 =
                          FStar_All.pipe_right pats
                            (FStar_Util.fold_map
                               (fun compat  ->
                                  fun br  ->
                                    let uu____78838 =
                                      FStar_Syntax_Subst.open_branch br  in
                                    match uu____78838 with
                                    | (pat,when_opt,branch1) ->
                                        let uu____78883 =
                                          extract_pat g pat t_e
                                            term_as_mlexpr
                                           in
                                        (match uu____78883 with
                                         | (env,p,pat_t_compat) ->
                                             let uu____78945 =
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
                                                   let uu____78968 =
                                                     term_as_mlexpr env w  in
                                                   (match uu____78968 with
                                                    | (w1,f_w,t_w) ->
                                                        let w2 =
                                                          maybe_coerce w_pos
                                                            env w1 t_w
                                                            FStar_Extraction_ML_Syntax.ml_bool_ty
                                                           in
                                                        ((FStar_Pervasives_Native.Some
                                                            w2), f_w))
                                                in
                                             (match uu____78945 with
                                              | (when_opt1,f_when) ->
                                                  let uu____79018 =
                                                    term_as_mlexpr env
                                                      branch1
                                                     in
                                                  (match uu____79018 with
                                                   | (mlbranch,f_branch,t_branch)
                                                       ->
                                                       let uu____79053 =
                                                         FStar_All.pipe_right
                                                           p
                                                           (FStar_List.map
                                                              (fun
                                                                 uu____79130 
                                                                 ->
                                                                 match uu____79130
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
                                                         uu____79053)))))
                               true)
                           in
                        match uu____78739 with
                        | (pat_t_compat,mlbranches) ->
                            let mlbranches1 = FStar_List.flatten mlbranches
                               in
                            let e1 =
                              if pat_t_compat
                              then e
                              else
                                (FStar_Extraction_ML_UEnv.debug g
                                   (fun uu____79301  ->
                                      let uu____79302 =
                                        FStar_Extraction_ML_Code.string_of_mlexpr
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          e
                                         in
                                      let uu____79304 =
                                        FStar_Extraction_ML_Code.string_of_mlty
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          t_e
                                         in
                                      FStar_Util.print2
                                        "Coercing scrutinee %s from type %s because pattern type is incompatible\n"
                                        uu____79302 uu____79304);
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty t_e)
                                   (FStar_Extraction_ML_Syntax.MLE_Coerce
                                      (e, t_e,
                                        FStar_Extraction_ML_Syntax.MLTY_Top)))
                               in
                            (match mlbranches1 with
                             | [] ->
                                 let uu____79331 =
                                   let uu____79332 =
                                     FStar_Syntax_Syntax.lid_as_fv
                                       FStar_Parser_Const.failwith_lid
                                       FStar_Syntax_Syntax.delta_constant
                                       FStar_Pervasives_Native.None
                                      in
                                   FStar_Extraction_ML_UEnv.lookup_fv g
                                     uu____79332
                                    in
                                 (match uu____79331 with
                                  | {
                                      FStar_Extraction_ML_UEnv.exp_b_name =
                                        uu____79339;
                                      FStar_Extraction_ML_UEnv.exp_b_expr =
                                        fw;
                                      FStar_Extraction_ML_UEnv.exp_b_tscheme
                                        = uu____79341;
                                      FStar_Extraction_ML_UEnv.exp_b_inst_ok
                                        = uu____79342;_}
                                      ->
                                      let uu____79345 =
                                        let uu____79346 =
                                          let uu____79347 =
                                            let uu____79354 =
                                              let uu____79357 =
                                                FStar_All.pipe_left
                                                  (FStar_Extraction_ML_Syntax.with_ty
                                                     FStar_Extraction_ML_Syntax.ml_string_ty)
                                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                                     (FStar_Extraction_ML_Syntax.MLC_String
                                                        "unreachable"))
                                                 in
                                              [uu____79357]  in
                                            (fw, uu____79354)  in
                                          FStar_Extraction_ML_Syntax.MLE_App
                                            uu____79347
                                           in
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             FStar_Extraction_ML_Syntax.ml_int_ty)
                                          uu____79346
                                         in
                                      (uu____79345,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        FStar_Extraction_ML_Syntax.ml_int_ty))
                             | (uu____79361,uu____79362,(uu____79363,f_first,t_first))::rest
                                 ->
                                 let uu____79423 =
                                   FStar_List.fold_left
                                     (fun uu____79465  ->
                                        fun uu____79466  ->
                                          match (uu____79465, uu____79466)
                                          with
                                          | ((topt,f),(uu____79523,uu____79524,
                                                       (uu____79525,f_branch,t_branch)))
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
                                                    let uu____79581 =
                                                      type_leq g t1 t_branch
                                                       in
                                                    if uu____79581
                                                    then
                                                      FStar_Pervasives_Native.Some
                                                        t_branch
                                                    else
                                                      (let uu____79588 =
                                                         type_leq g t_branch
                                                           t1
                                                          in
                                                       if uu____79588
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
                                 (match uu____79423 with
                                  | (topt,f_match) ->
                                      let mlbranches2 =
                                        FStar_All.pipe_right mlbranches1
                                          (FStar_List.map
                                             (fun uu____79686  ->
                                                match uu____79686 with
                                                | (p,(wopt,uu____79715),
                                                   (b1,uu____79717,t1)) ->
                                                    let b2 =
                                                      match topt with
                                                      | FStar_Pervasives_Native.None
                                                           ->
                                                          FStar_Extraction_ML_Syntax.apply_obj_repr
                                                            b1 t1
                                                      | FStar_Pervasives_Native.Some
                                                          uu____79736 -> b1
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
                                      let uu____79741 =
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             t_match)
                                          (FStar_Extraction_ML_Syntax.MLE_Match
                                             (e1, mlbranches2))
                                         in
                                      (uu____79741, f_match, t_match)))))))

let (ind_discriminator_body :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlmodule1)
  =
  fun env  ->
    fun discName  ->
      fun constrName  ->
        let uu____79768 =
          let uu____79773 =
            FStar_TypeChecker_Env.lookup_lid
              env.FStar_Extraction_ML_UEnv.env_tcenv discName
             in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____79773  in
        match uu____79768 with
        | (uu____79798,fstar_disc_type) ->
            let wildcards =
              let uu____79808 =
                let uu____79809 = FStar_Syntax_Subst.compress fstar_disc_type
                   in
                uu____79809.FStar_Syntax_Syntax.n  in
              match uu____79808 with
              | FStar_Syntax_Syntax.Tm_arrow (binders,uu____79820) ->
                  let uu____79841 =
                    FStar_All.pipe_right binders
                      (FStar_List.filter
                         (fun uu___620_79875  ->
                            match uu___620_79875 with
                            | (uu____79883,FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____79884)) ->
                                true
                            | uu____79889 -> false))
                     in
                  FStar_All.pipe_right uu____79841
                    (FStar_List.map
                       (fun uu____79925  ->
                          let uu____79932 = fresh "_"  in
                          (uu____79932, FStar_Extraction_ML_Syntax.MLTY_Top)))
              | uu____79936 -> failwith "Discriminator must be a function"
               in
            let mlid = fresh "_discr_"  in
            let targ = FStar_Extraction_ML_Syntax.MLTY_Top  in
            let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top  in
            let discrBody =
              let uu____79951 =
                let uu____79952 =
                  let uu____79964 =
                    let uu____79965 =
                      let uu____79966 =
                        let uu____79981 =
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty targ)
                            (FStar_Extraction_ML_Syntax.MLE_Name ([], mlid))
                           in
                        let uu____79987 =
                          let uu____79998 =
                            let uu____80007 =
                              let uu____80008 =
                                let uu____80015 =
                                  FStar_Extraction_ML_Syntax.mlpath_of_lident
                                    constrName
                                   in
                                (uu____80015,
                                  [FStar_Extraction_ML_Syntax.MLP_Wild])
                                 in
                              FStar_Extraction_ML_Syntax.MLP_CTor uu____80008
                               in
                            let uu____80018 =
                              FStar_All.pipe_left
                                (FStar_Extraction_ML_Syntax.with_ty
                                   FStar_Extraction_ML_Syntax.ml_bool_ty)
                                (FStar_Extraction_ML_Syntax.MLE_Const
                                   (FStar_Extraction_ML_Syntax.MLC_Bool true))
                               in
                            (uu____80007, FStar_Pervasives_Native.None,
                              uu____80018)
                             in
                          let uu____80022 =
                            let uu____80033 =
                              let uu____80042 =
                                FStar_All.pipe_left
                                  (FStar_Extraction_ML_Syntax.with_ty
                                     FStar_Extraction_ML_Syntax.ml_bool_ty)
                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                     (FStar_Extraction_ML_Syntax.MLC_Bool
                                        false))
                                 in
                              (FStar_Extraction_ML_Syntax.MLP_Wild,
                                FStar_Pervasives_Native.None, uu____80042)
                               in
                            [uu____80033]  in
                          uu____79998 :: uu____80022  in
                        (uu____79981, uu____79987)  in
                      FStar_Extraction_ML_Syntax.MLE_Match uu____79966  in
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.ml_bool_ty) uu____79965
                     in
                  ((FStar_List.append wildcards [(mlid, targ)]), uu____79964)
                   in
                FStar_Extraction_ML_Syntax.MLE_Fun uu____79952  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty disc_ty) uu____79951
               in
            let uu____80103 =
              let uu____80104 =
                let uu____80107 =
                  let uu____80108 =
                    FStar_Extraction_ML_UEnv.convIdent
                      discName.FStar_Ident.ident
                     in
                  {
                    FStar_Extraction_ML_Syntax.mllb_name = uu____80108;
                    FStar_Extraction_ML_Syntax.mllb_tysc =
                      FStar_Pervasives_Native.None;
                    FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                    FStar_Extraction_ML_Syntax.mllb_def = discrBody;
                    FStar_Extraction_ML_Syntax.mllb_meta = [];
                    FStar_Extraction_ML_Syntax.print_typ = false
                  }  in
                [uu____80107]  in
              (FStar_Extraction_ML_Syntax.NonRec, uu____80104)  in
            FStar_Extraction_ML_Syntax.MLM_Let uu____80103
  