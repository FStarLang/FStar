open Prims
exception Un_extractable 
let (uu___is_Un_extractable : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Un_extractable  -> true | uu____65803 -> false
  
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
  'Auu____65872 .
    FStar_Ident.ident Prims.list ->
      'Auu____65872 Prims.list -> (Prims.string * 'Auu____65872) Prims.list
  =
  fun fs  ->
    fun vs  ->
      FStar_List.map2 (fun f  -> fun e  -> ((f.FStar_Ident.idText), e)) fs vs
  
let fail :
  'Auu____65915 .
    FStar_Range.range ->
      (FStar_Errors.raw_error * Prims.string) -> 'Auu____65915
  = fun r  -> fun err  -> FStar_Errors.raise_error err r 
let err_uninst :
  'Auu____65947 .
    FStar_Extraction_ML_UEnv.uenv ->
      FStar_Syntax_Syntax.term ->
        (Prims.string Prims.list * FStar_Extraction_ML_Syntax.mlty) ->
          FStar_Syntax_Syntax.term -> 'Auu____65947
  =
  fun env  ->
    fun t  ->
      fun uu____65973  ->
        fun app  ->
          match uu____65973 with
          | (vars,ty) ->
              let uu____65990 =
                let uu____65996 =
                  let uu____65998 = FStar_Syntax_Print.term_to_string t  in
                  let uu____66000 =
                    FStar_All.pipe_right vars (FStar_String.concat ", ")  in
                  let uu____66007 =
                    FStar_Extraction_ML_Code.string_of_mlty
                      env.FStar_Extraction_ML_UEnv.currentModule ty
                     in
                  let uu____66009 = FStar_Syntax_Print.term_to_string app  in
                  FStar_Util.format4
                    "Variable %s has a polymorphic type (forall %s. %s); expected it to be fully instantiated, but got %s"
                    uu____65998 uu____66000 uu____66007 uu____66009
                   in
                (FStar_Errors.Fatal_Uninstantiated, uu____65996)  in
              fail t.FStar_Syntax_Syntax.pos uu____65990
  
let err_ill_typed_application :
  'Auu____66028 'Auu____66029 .
    FStar_Extraction_ML_UEnv.uenv ->
      FStar_Syntax_Syntax.term ->
        FStar_Extraction_ML_Syntax.mlexpr ->
          (FStar_Syntax_Syntax.term * 'Auu____66028) Prims.list ->
            FStar_Extraction_ML_Syntax.mlty -> 'Auu____66029
  =
  fun env  ->
    fun t  ->
      fun mlhead  ->
        fun args  ->
          fun ty  ->
            let uu____66067 =
              let uu____66073 =
                let uu____66075 = FStar_Syntax_Print.term_to_string t  in
                let uu____66077 =
                  FStar_Extraction_ML_Code.string_of_mlexpr
                    env.FStar_Extraction_ML_UEnv.currentModule mlhead
                   in
                let uu____66079 =
                  FStar_Extraction_ML_Code.string_of_mlty
                    env.FStar_Extraction_ML_UEnv.currentModule ty
                   in
                let uu____66081 =
                  let uu____66083 =
                    FStar_All.pipe_right args
                      (FStar_List.map
                         (fun uu____66104  ->
                            match uu____66104 with
                            | (x,uu____66111) ->
                                FStar_Syntax_Print.term_to_string x))
                     in
                  FStar_All.pipe_right uu____66083 (FStar_String.concat " ")
                   in
                FStar_Util.format4
                  "Ill-typed application: source application is %s \n translated prefix to %s at type %s\n remaining args are %s\n"
                  uu____66075 uu____66077 uu____66079 uu____66081
                 in
              (FStar_Errors.Fatal_IllTyped, uu____66073)  in
            fail t.FStar_Syntax_Syntax.pos uu____66067
  
let err_ill_typed_erasure :
  'Auu____66128 .
    FStar_Extraction_ML_UEnv.uenv ->
      FStar_Range.range -> FStar_Extraction_ML_Syntax.mlty -> 'Auu____66128
  =
  fun env  ->
    fun pos  ->
      fun ty  ->
        let uu____66144 =
          let uu____66150 =
            let uu____66152 =
              FStar_Extraction_ML_Code.string_of_mlty
                env.FStar_Extraction_ML_UEnv.currentModule ty
               in
            FStar_Util.format1
              "Erased value found where a value of type %s was expected"
              uu____66152
             in
          (FStar_Errors.Fatal_IllTyped, uu____66150)  in
        fail pos uu____66144
  
let err_value_restriction :
  'Auu____66161 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> 'Auu____66161
  =
  fun t  ->
    let uu____66171 =
      let uu____66177 =
        let uu____66179 = FStar_Syntax_Print.tag_of_term t  in
        let uu____66181 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format2
          "Refusing to generalize because of the value restriction: (%s) %s"
          uu____66179 uu____66181
         in
      (FStar_Errors.Fatal_ValueRestriction, uu____66177)  in
    fail t.FStar_Syntax_Syntax.pos uu____66171
  
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
            let uu____66215 =
              let uu____66221 =
                let uu____66223 = FStar_Syntax_Print.term_to_string t  in
                let uu____66225 =
                  FStar_Extraction_ML_Code.string_of_mlty
                    env.FStar_Extraction_ML_UEnv.currentModule ty
                   in
                let uu____66227 = FStar_Extraction_ML_Util.eff_to_string f0
                   in
                let uu____66229 = FStar_Extraction_ML_Util.eff_to_string f1
                   in
                FStar_Util.format4
                  "for expression %s of type %s, Expected effect %s; got effect %s"
                  uu____66223 uu____66225 uu____66227 uu____66229
                 in
              (FStar_Errors.Warning_ExtractionUnexpectedEffect, uu____66221)
               in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____66215
  
let (effect_as_etag :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Ident.lident -> FStar_Extraction_ML_Syntax.e_tag)
  =
  let cache = FStar_Util.smap_create (Prims.parse_int "20")  in
  let rec delta_norm_eff g l =
    let uu____66257 = FStar_Util.smap_try_find cache l.FStar_Ident.str  in
    match uu____66257 with
    | FStar_Pervasives_Native.Some l1 -> l1
    | FStar_Pervasives_Native.None  ->
        let res =
          let uu____66262 =
            FStar_TypeChecker_Env.lookup_effect_abbrev
              g.FStar_Extraction_ML_UEnv.env_tcenv
              [FStar_Syntax_Syntax.U_zero] l
             in
          match uu____66262 with
          | FStar_Pervasives_Native.None  -> l
          | FStar_Pervasives_Native.Some (uu____66273,c) ->
              delta_norm_eff g (FStar_Syntax_Util.comp_effect_name c)
           in
        (FStar_Util.smap_add cache l.FStar_Ident.str res; res)
     in
  fun g  ->
    fun l  ->
      let l1 = delta_norm_eff g l  in
      let uu____66283 =
        FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid  in
      if uu____66283
      then FStar_Extraction_ML_Syntax.E_PURE
      else
        (let uu____66288 =
           FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GHOST_lid  in
         if uu____66288
         then FStar_Extraction_ML_Syntax.E_GHOST
         else
           (let ed_opt =
              FStar_TypeChecker_Env.effect_decl_opt
                g.FStar_Extraction_ML_UEnv.env_tcenv l1
               in
            match ed_opt with
            | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                let uu____66314 =
                  FStar_TypeChecker_Env.is_reifiable_effect
                    g.FStar_Extraction_ML_UEnv.env_tcenv
                    ed.FStar_Syntax_Syntax.mname
                   in
                if uu____66314
                then FStar_Extraction_ML_Syntax.E_PURE
                else FStar_Extraction_ML_Syntax.E_IMPURE
            | FStar_Pervasives_Native.None  ->
                FStar_Extraction_ML_Syntax.E_IMPURE))
  
let rec (is_arity :
  FStar_Extraction_ML_UEnv.uenv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t  in
      let uu____66338 =
        let uu____66339 = FStar_Syntax_Subst.compress t1  in
        uu____66339.FStar_Syntax_Syntax.n  in
      match uu____66338 with
      | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____66345 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_ascribed uu____66370 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_meta uu____66399 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____66409 = FStar_Syntax_Util.unfold_lazy i  in
          is_arity env uu____66409
      | FStar_Syntax_Syntax.Tm_uvar uu____66410 -> false
      | FStar_Syntax_Syntax.Tm_constant uu____66424 -> false
      | FStar_Syntax_Syntax.Tm_name uu____66426 -> false
      | FStar_Syntax_Syntax.Tm_quoted uu____66428 -> false
      | FStar_Syntax_Syntax.Tm_bvar uu____66436 -> false
      | FStar_Syntax_Syntax.Tm_type uu____66438 -> true
      | FStar_Syntax_Syntax.Tm_arrow (uu____66440,c) ->
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
           | FStar_Pervasives_Native.Some (uu____66476,t2) -> is_arity env t2)
      | FStar_Syntax_Syntax.Tm_app uu____66482 ->
          let uu____66499 = FStar_Syntax_Util.head_and_args t1  in
          (match uu____66499 with | (head1,uu____66518) -> is_arity env head1)
      | FStar_Syntax_Syntax.Tm_uinst (head1,uu____66544) ->
          is_arity env head1
      | FStar_Syntax_Syntax.Tm_refine (x,uu____66550) ->
          is_arity env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_abs (uu____66555,body,uu____66557) ->
          is_arity env body
      | FStar_Syntax_Syntax.Tm_let (uu____66582,body) -> is_arity env body
      | FStar_Syntax_Syntax.Tm_match (uu____66602,branches) ->
          (match branches with
           | (uu____66641,uu____66642,e)::uu____66644 -> is_arity env e
           | uu____66691 -> false)
  
let rec (is_type_aux :
  FStar_Extraction_ML_UEnv.uenv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____66723 ->
          let uu____66746 =
            let uu____66748 = FStar_Syntax_Print.tag_of_term t1  in
            FStar_Util.format1 "Impossible: %s" uu____66748  in
          failwith uu____66746
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____66752 =
            let uu____66754 = FStar_Syntax_Print.tag_of_term t1  in
            FStar_Util.format1 "Impossible: %s" uu____66754  in
          failwith uu____66752
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____66759 = FStar_Syntax_Util.unfold_lazy i  in
          is_type_aux env uu____66759
      | FStar_Syntax_Syntax.Tm_constant uu____66760 -> false
      | FStar_Syntax_Syntax.Tm_type uu____66762 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____66764 -> true
      | FStar_Syntax_Syntax.Tm_arrow uu____66772 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.failwith_lid ->
          false
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Extraction_ML_UEnv.is_type_name env fv
      | FStar_Syntax_Syntax.Tm_uvar
          ({ FStar_Syntax_Syntax.ctx_uvar_head = uu____66791;
             FStar_Syntax_Syntax.ctx_uvar_gamma = uu____66792;
             FStar_Syntax_Syntax.ctx_uvar_binders = uu____66793;
             FStar_Syntax_Syntax.ctx_uvar_typ = t2;
             FStar_Syntax_Syntax.ctx_uvar_reason = uu____66795;
             FStar_Syntax_Syntax.ctx_uvar_should_check = uu____66796;
             FStar_Syntax_Syntax.ctx_uvar_range = uu____66797;
             FStar_Syntax_Syntax.ctx_uvar_meta = uu____66798;_},s)
          ->
          let uu____66847 = FStar_Syntax_Subst.subst' s t2  in
          is_arity env uu____66847
      | FStar_Syntax_Syntax.Tm_bvar
          { FStar_Syntax_Syntax.ppname = uu____66848;
            FStar_Syntax_Syntax.index = uu____66849;
            FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_name
          { FStar_Syntax_Syntax.ppname = uu____66854;
            FStar_Syntax_Syntax.index = uu____66855;
            FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____66861,uu____66862) ->
          is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____66904) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____66911) ->
          let uu____66936 = FStar_Syntax_Subst.open_term bs body  in
          (match uu____66936 with
           | (uu____66942,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
          let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
          let uu____66962 =
            let uu____66967 =
              let uu____66968 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____66968]  in
            FStar_Syntax_Subst.open_term uu____66967 body  in
          (match uu____66962 with
           | (uu____66988,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_let ((uu____66990,lbs),body) ->
          let uu____67010 = FStar_Syntax_Subst.open_let_rec lbs body  in
          (match uu____67010 with
           | (uu____67018,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_match (uu____67024,branches) ->
          (match branches with
           | b::uu____67064 ->
               let uu____67109 = FStar_Syntax_Subst.open_branch b  in
               (match uu____67109 with
                | (uu____67111,uu____67112,e) -> is_type_aux env e)
           | uu____67130 -> false)
      | FStar_Syntax_Syntax.Tm_quoted uu____67148 -> false
      | FStar_Syntax_Syntax.Tm_meta (t2,uu____67157) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_app (head1,uu____67163) ->
          is_type_aux env head1
  
let (is_type :
  FStar_Extraction_ML_UEnv.uenv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      FStar_Extraction_ML_UEnv.debug env
        (fun uu____67204  ->
           let uu____67205 = FStar_Syntax_Print.tag_of_term t  in
           let uu____67207 = FStar_Syntax_Print.term_to_string t  in
           FStar_Util.print2 "checking is_type (%s) %s\n" uu____67205
             uu____67207);
      (let b = is_type_aux env t  in
       FStar_Extraction_ML_UEnv.debug env
         (fun uu____67216  ->
            if b
            then
              let uu____67218 = FStar_Syntax_Print.term_to_string t  in
              let uu____67220 = FStar_Syntax_Print.tag_of_term t  in
              FStar_Util.print2 "yes, is_type %s (%s)\n" uu____67218
                uu____67220
            else
              (let uu____67225 = FStar_Syntax_Print.term_to_string t  in
               let uu____67227 = FStar_Syntax_Print.tag_of_term t  in
               FStar_Util.print2 "not a type %s (%s)\n" uu____67225
                 uu____67227));
       b)
  
let is_type_binder :
  'Auu____67237 .
    FStar_Extraction_ML_UEnv.uenv ->
      (FStar_Syntax_Syntax.bv * 'Auu____67237) -> Prims.bool
  =
  fun env  ->
    fun x  ->
      is_arity env (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
  
let (is_constructor : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____67264 =
      let uu____67265 = FStar_Syntax_Subst.compress t  in
      uu____67265.FStar_Syntax_Syntax.n  in
    match uu____67264 with
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____67269;
          FStar_Syntax_Syntax.fv_delta = uu____67270;
          FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
            (FStar_Syntax_Syntax.Data_ctor );_}
        -> true
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____67272;
          FStar_Syntax_Syntax.fv_delta = uu____67273;
          FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
            (FStar_Syntax_Syntax.Record_ctor uu____67274);_}
        -> true
    | uu____67282 -> false
  
let rec (is_fstar_value : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____67291 =
      let uu____67292 = FStar_Syntax_Subst.compress t  in
      uu____67292.FStar_Syntax_Syntax.n  in
    match uu____67291 with
    | FStar_Syntax_Syntax.Tm_constant uu____67296 -> true
    | FStar_Syntax_Syntax.Tm_bvar uu____67298 -> true
    | FStar_Syntax_Syntax.Tm_fvar uu____67300 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____67302 -> true
    | FStar_Syntax_Syntax.Tm_app (head1,args) ->
        let uu____67348 = is_constructor head1  in
        if uu____67348
        then
          FStar_All.pipe_right args
            (FStar_List.for_all
               (fun uu____67370  ->
                  match uu____67370 with
                  | (te,uu____67379) -> is_fstar_value te))
        else false
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____67388) -> is_fstar_value t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____67394,uu____67395) ->
        is_fstar_value t1
    | uu____67436 -> false
  
let rec (is_ml_value : FStar_Extraction_ML_Syntax.mlexpr -> Prims.bool) =
  fun e  ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_Const uu____67446 -> true
    | FStar_Extraction_ML_Syntax.MLE_Var uu____67448 -> true
    | FStar_Extraction_ML_Syntax.MLE_Name uu____67451 -> true
    | FStar_Extraction_ML_Syntax.MLE_Fun uu____67453 -> true
    | FStar_Extraction_ML_Syntax.MLE_CTor (uu____67466,exps) ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Tuple exps ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Record (uu____67475,fields) ->
        FStar_Util.for_all
          (fun uu____67505  ->
             match uu____67505 with | (uu____67512,e1) -> is_ml_value e1)
          fields
    | FStar_Extraction_ML_Syntax.MLE_TApp (h,uu____67517) -> is_ml_value h
    | uu____67522 -> false
  
let (fresh : Prims.string -> Prims.string) =
  let c = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun x  ->
    FStar_Util.incr c;
    (let uu____67540 =
       let uu____67542 = FStar_ST.op_Bang c  in
       FStar_Util.string_of_int uu____67542  in
     Prims.op_Hat x uu____67540)
  
let (normalize_abs : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t0  ->
    let rec aux bs t copt =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_abs (bs',body,copt1) ->
          aux (FStar_List.append bs bs') body copt1
      | uu____67645 ->
          let e' = FStar_Syntax_Util.unascribe t1  in
          let uu____67647 = FStar_Syntax_Util.is_fun e'  in
          if uu____67647
          then aux bs e' copt
          else FStar_Syntax_Util.abs bs e' copt
       in
    aux [] t0 FStar_Pervasives_Native.None
  
let (unit_binder : FStar_Syntax_Syntax.binder) =
  let uu____67661 =
    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
      FStar_Syntax_Syntax.t_unit
     in
  FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____67661 
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
      (let uu____67752 = FStar_List.hd l  in
       match uu____67752 with
       | (p1,w1,e1) ->
           let uu____67787 =
             let uu____67796 = FStar_List.tl l  in FStar_List.hd uu____67796
              in
           (match uu____67787 with
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
                 | uu____67880 -> def)))
  
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
      let uu____67919 = FStar_Extraction_ML_Util.doms_and_cod t  in
      match uu____67919 with
      | (ts,r) ->
          if ts = []
          then e
          else
            (let vs = FStar_List.map (fun uu____67943  -> fresh "a") ts  in
             let vs_ts = FStar_List.zip vs ts  in
             let vs_es =
               let uu____67957 = FStar_List.zip vs ts  in
               FStar_List.map
                 (fun uu____67974  ->
                    match uu____67974 with
                    | (v1,t1) ->
                        FStar_Extraction_ML_Syntax.with_ty t1
                          (FStar_Extraction_ML_Syntax.MLE_Var v1))
                 uu____67957
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
      let uu____68005 = FStar_Extraction_ML_Util.doms_and_cod t  in
      match uu____68005 with
      | (ts,r) ->
          let body r1 =
            let r2 =
              let uu____68025 = FStar_Extraction_ML_Util.udelta_unfold g r1
                 in
              match uu____68025 with
              | FStar_Pervasives_Native.None  -> r1
              | FStar_Pervasives_Native.Some r2 -> r2  in
            match r2 with
            | FStar_Extraction_ML_Syntax.MLTY_Erased  ->
                FStar_Extraction_ML_Syntax.ml_unit
            | FStar_Extraction_ML_Syntax.MLTY_Top  ->
                FStar_Extraction_ML_Syntax.apply_obj_repr
                  FStar_Extraction_ML_Syntax.ml_unit
                  FStar_Extraction_ML_Syntax.MLTY_Erased
            | uu____68029 ->
                FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty r2)
                  (FStar_Extraction_ML_Syntax.MLE_Coerce
                     (FStar_Extraction_ML_Syntax.ml_unit,
                       FStar_Extraction_ML_Syntax.MLTY_Erased, r2))
             in
          if ts = []
          then body r
          else
            (let vs = FStar_List.map (fun uu____68041  -> fresh "a") ts  in
             let vs_ts = FStar_List.zip vs ts  in
             let uu____68052 =
               let uu____68053 =
                 let uu____68065 = body r  in (vs_ts, uu____68065)  in
               FStar_Extraction_ML_Syntax.MLE_Fun uu____68053  in
             FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t)
               uu____68052)
  
let (maybe_eta_expand :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun expect  ->
    fun e  ->
      let uu____68084 =
        (FStar_Options.ml_no_eta_expand_coertions ()) ||
          (let uu____68087 = FStar_Options.codegen ()  in
           uu____68087 = (FStar_Pervasives_Native.Some FStar_Options.Kremlin))
         in
      if uu____68084 then e else eta_expand expect e
  
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
            | uu____68165 ->
                FStar_Extraction_ML_Syntax.MLE_Fun ([binder], body)
             in
          let rec aux e1 ty1 expect1 =
            let coerce_branch uu____68220 =
              match uu____68220 with
              | (pat,w,b) ->
                  let uu____68244 = aux b ty1 expect1  in
                  (pat, w, uu____68244)
               in
            match ((e1.FStar_Extraction_ML_Syntax.expr), ty1, expect1) with
            | (FStar_Extraction_ML_Syntax.MLE_Fun
               (arg::rest,body),FStar_Extraction_ML_Syntax.MLTY_Fun
               (t0,uu____68251,t1),FStar_Extraction_ML_Syntax.MLTY_Fun
               (s0,uu____68254,s1)) ->
                let body1 =
                  match rest with
                  | [] -> body
                  | uu____68286 ->
                      FStar_Extraction_ML_Syntax.with_ty t1
                        (FStar_Extraction_ML_Syntax.MLE_Fun (rest, body))
                   in
                let body2 = aux body1 t1 s1  in
                let uu____68302 = type_leq g s0 t0  in
                if uu____68302
                then
                  FStar_Extraction_ML_Syntax.with_ty expect1
                    (mk_fun arg body2)
                else
                  (let lb =
                     let uu____68308 =
                       let uu____68309 =
                         let uu____68310 =
                           let uu____68317 =
                             FStar_All.pipe_left
                               (FStar_Extraction_ML_Syntax.with_ty s0)
                               (FStar_Extraction_ML_Syntax.MLE_Var
                                  (FStar_Pervasives_Native.fst arg))
                              in
                           (uu____68317, s0, t0)  in
                         FStar_Extraction_ML_Syntax.MLE_Coerce uu____68310
                          in
                       FStar_Extraction_ML_Syntax.with_ty t0 uu____68309  in
                     {
                       FStar_Extraction_ML_Syntax.mllb_name =
                         (FStar_Pervasives_Native.fst arg);
                       FStar_Extraction_ML_Syntax.mllb_tysc =
                         (FStar_Pervasives_Native.Some ([], t0));
                       FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                       FStar_Extraction_ML_Syntax.mllb_def = uu____68308;
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
               (lbs,body),uu____68336,uu____68337) ->
                let uu____68350 =
                  let uu____68351 =
                    let uu____68362 = aux body ty1 expect1  in
                    (lbs, uu____68362)  in
                  FStar_Extraction_ML_Syntax.MLE_Let uu____68351  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____68350
            | (FStar_Extraction_ML_Syntax.MLE_Match
               (s,branches),uu____68371,uu____68372) ->
                let uu____68393 =
                  let uu____68394 =
                    let uu____68409 = FStar_List.map coerce_branch branches
                       in
                    (s, uu____68409)  in
                  FStar_Extraction_ML_Syntax.MLE_Match uu____68394  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____68393
            | (FStar_Extraction_ML_Syntax.MLE_If
               (s,b1,b2_opt),uu____68449,uu____68450) ->
                let uu____68455 =
                  let uu____68456 =
                    let uu____68465 = aux b1 ty1 expect1  in
                    let uu____68466 =
                      FStar_Util.map_opt b2_opt
                        (fun b2  -> aux b2 ty1 expect1)
                       in
                    (s, uu____68465, uu____68466)  in
                  FStar_Extraction_ML_Syntax.MLE_If uu____68456  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____68455
            | (FStar_Extraction_ML_Syntax.MLE_Seq es,uu____68474,uu____68475)
                ->
                let uu____68478 = FStar_Util.prefix es  in
                (match uu____68478 with
                 | (prefix1,last1) ->
                     let uu____68491 =
                       let uu____68492 =
                         let uu____68495 =
                           let uu____68498 = aux last1 ty1 expect1  in
                           [uu____68498]  in
                         FStar_List.append prefix1 uu____68495  in
                       FStar_Extraction_ML_Syntax.MLE_Seq uu____68492  in
                     FStar_All.pipe_left
                       (FStar_Extraction_ML_Syntax.with_ty expect1)
                       uu____68491)
            | (FStar_Extraction_ML_Syntax.MLE_Try
               (s,branches),uu____68501,uu____68502) ->
                let uu____68523 =
                  let uu____68524 =
                    let uu____68539 = FStar_List.map coerce_branch branches
                       in
                    (s, uu____68539)  in
                  FStar_Extraction_ML_Syntax.MLE_Try uu____68524  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____68523
            | uu____68576 ->
                FStar_Extraction_ML_Syntax.with_ty expect1
                  (FStar_Extraction_ML_Syntax.MLE_Coerce (e1, ty1, expect1))
             in
          aux e ty expect
  
let maybe_coerce :
  'Auu____68596 .
    'Auu____68596 ->
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
            let uu____68623 =
              type_leq_c g (FStar_Pervasives_Native.Some e) ty1 expect  in
            match uu____68623 with
            | (true ,FStar_Pervasives_Native.Some e') -> e'
            | uu____68636 ->
                (match ty1 with
                 | FStar_Extraction_ML_Syntax.MLTY_Erased  ->
                     default_value_for_ty g expect
                 | uu____68644 ->
                     let uu____68645 =
                       let uu____68647 =
                         FStar_Extraction_ML_Util.erase_effect_annotations
                           ty1
                          in
                       let uu____68648 =
                         FStar_Extraction_ML_Util.erase_effect_annotations
                           expect
                          in
                       type_leq g uu____68647 uu____68648  in
                     if uu____68645
                     then
                       (FStar_Extraction_ML_UEnv.debug g
                          (fun uu____68654  ->
                             let uu____68655 =
                               FStar_Extraction_ML_Code.string_of_mlexpr
                                 g.FStar_Extraction_ML_UEnv.currentModule e
                                in
                             let uu____68657 =
                               FStar_Extraction_ML_Code.string_of_mlty
                                 g.FStar_Extraction_ML_UEnv.currentModule ty1
                                in
                             FStar_Util.print2
                               "\n Effect mismatch on type of %s : %s\n"
                               uu____68655 uu____68657);
                        e)
                     else
                       (FStar_Extraction_ML_UEnv.debug g
                          (fun uu____68667  ->
                             let uu____68668 =
                               FStar_Extraction_ML_Code.string_of_mlexpr
                                 g.FStar_Extraction_ML_UEnv.currentModule e
                                in
                             let uu____68670 =
                               FStar_Extraction_ML_Code.string_of_mlty
                                 g.FStar_Extraction_ML_UEnv.currentModule ty1
                                in
                             let uu____68672 =
                               FStar_Extraction_ML_Code.string_of_mlty
                                 g.FStar_Extraction_ML_UEnv.currentModule
                                 expect
                                in
                             FStar_Util.print3
                               "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n"
                               uu____68668 uu____68670 uu____68672);
                        (let uu____68675 = apply_coercion g e ty1 expect  in
                         maybe_eta_expand expect uu____68675)))
  
let (bv_as_mlty :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun bv  ->
      let uu____68687 = FStar_Extraction_ML_UEnv.lookup_bv g bv  in
      match uu____68687 with
      | FStar_Util.Inl ty_b -> ty_b.FStar_Extraction_ML_UEnv.ty_b_ty
      | uu____68689 -> FStar_Extraction_ML_Syntax.MLTY_Top
  
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
    | FStar_Syntax_Syntax.Total uu____68707 -> c
    | FStar_Syntax_Syntax.GTotal uu____68716 -> c
    | FStar_Syntax_Syntax.Comp ct ->
        let effect_args =
          FStar_List.map
            (fun uu____68752  ->
               match uu____68752 with
               | (uu____68767,aq) -> (FStar_Syntax_Syntax.t_unit, aq))
            ct.FStar_Syntax_Syntax.effect_args
           in
        let ct1 =
          let uu___1131_68780 = ct  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___1131_68780.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___1131_68780.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ =
              (uu___1131_68780.FStar_Syntax_Syntax.result_typ);
            FStar_Syntax_Syntax.effect_args = effect_args;
            FStar_Syntax_Syntax.flags =
              (uu___1131_68780.FStar_Syntax_Syntax.flags)
          }  in
        let c1 =
          let uu___1134_68784 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
            FStar_Syntax_Syntax.pos =
              (uu___1134_68784.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___1134_68784.FStar_Syntax_Syntax.vars)
          }  in
        c1
  
let rec (translate_term_to_mlty :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun t0  ->
      let arg_as_mlty g1 uu____68833 =
        match uu____68833 with
        | (a,uu____68841) ->
            let uu____68846 = is_type g1 a  in
            if uu____68846
            then translate_term_to_mlty g1 a
            else FStar_Extraction_ML_UEnv.erasedContent
         in
      let fv_app_as_mlty g1 fv args =
        let uu____68867 =
          let uu____68869 = FStar_Extraction_ML_UEnv.is_fv_type g1 fv  in
          Prims.op_Negation uu____68869  in
        if uu____68867
        then FStar_Extraction_ML_Syntax.MLTY_Top
        else
          (let uu____68874 =
             let uu____68889 =
               FStar_TypeChecker_Env.lookup_lid
                 g1.FStar_Extraction_ML_UEnv.env_tcenv
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             match uu____68889 with
             | ((uu____68912,fvty),uu____68914) ->
                 let fvty1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Env.UnfoldUntil
                        FStar_Syntax_Syntax.delta_constant]
                     g1.FStar_Extraction_ML_UEnv.env_tcenv fvty
                    in
                 FStar_Syntax_Util.arrow_formals fvty1
              in
           match uu____68874 with
           | (formals,uu____68921) ->
               let mlargs = FStar_List.map (arg_as_mlty g1) args  in
               let mlargs1 =
                 let n_args = FStar_List.length args  in
                 if (FStar_List.length formals) > n_args
                 then
                   let uu____68974 = FStar_Util.first_N n_args formals  in
                   match uu____68974 with
                   | (uu____69003,rest) ->
                       let uu____69037 =
                         FStar_List.map
                           (fun uu____69047  ->
                              FStar_Extraction_ML_UEnv.erasedContent) rest
                          in
                       FStar_List.append mlargs uu____69037
                 else mlargs  in
               let nm =
                 let uu____69057 =
                   FStar_Extraction_ML_UEnv.maybe_mangle_type_projector g1 fv
                    in
                 match uu____69057 with
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
        | FStar_Syntax_Syntax.Tm_type uu____69075 ->
            FStar_Extraction_ML_Syntax.MLTY_Erased
        | FStar_Syntax_Syntax.Tm_bvar uu____69076 ->
            let uu____69077 =
              let uu____69079 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____69079
               in
            failwith uu____69077
        | FStar_Syntax_Syntax.Tm_delayed uu____69082 ->
            let uu____69105 =
              let uu____69107 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____69107
               in
            failwith uu____69105
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____69110 =
              let uu____69112 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____69112
               in
            failwith uu____69110
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____69116 = FStar_Syntax_Util.unfold_lazy i  in
            translate_term_to_mlty env uu____69116
        | FStar_Syntax_Syntax.Tm_constant uu____69117 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_quoted uu____69118 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_uvar uu____69125 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_meta (t2,uu____69139) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____69144;
               FStar_Syntax_Syntax.index = uu____69145;
               FStar_Syntax_Syntax.sort = t2;_},uu____69147)
            -> translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_uinst (t2,uu____69156) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____69162,uu____69163) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
        | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv []
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let uu____69236 = FStar_Syntax_Subst.open_comp bs c  in
            (match uu____69236 with
             | (bs1,c1) ->
                 let uu____69243 = binders_as_ml_binders env bs1  in
                 (match uu____69243 with
                  | (mlbs,env1) ->
                      let t_ret =
                        let eff =
                          FStar_TypeChecker_Env.norm_eff_name
                            env1.FStar_Extraction_ML_UEnv.env_tcenv
                            (FStar_Syntax_Util.comp_effect_name c1)
                           in
                        let c2 = comp_no_args c1  in
                        let uu____69276 =
                          let uu____69283 =
                            FStar_TypeChecker_Env.effect_decl_opt
                              env1.FStar_Extraction_ML_UEnv.env_tcenv eff
                             in
                          FStar_Util.must uu____69283  in
                        match uu____69276 with
                        | (ed,qualifiers) ->
                            let uu____69304 =
                              FStar_TypeChecker_Env.is_reifiable_effect
                                g.FStar_Extraction_ML_UEnv.env_tcenv
                                ed.FStar_Syntax_Syntax.mname
                               in
                            if uu____69304
                            then
                              let t2 =
                                FStar_TypeChecker_Env.reify_comp
                                  env1.FStar_Extraction_ML_UEnv.env_tcenv c2
                                  FStar_Syntax_Syntax.U_unknown
                                 in
                              (FStar_Extraction_ML_UEnv.debug env1
                                 (fun uu____69312  ->
                                    let uu____69313 =
                                      FStar_Syntax_Print.comp_to_string c2
                                       in
                                    let uu____69315 =
                                      FStar_Syntax_Print.term_to_string t2
                                       in
                                    FStar_Util.print2
                                      "Translating comp type %s as %s\n"
                                      uu____69313 uu____69315);
                               (let res = translate_term_to_mlty env1 t2  in
                                FStar_Extraction_ML_UEnv.debug env1
                                  (fun uu____69324  ->
                                     let uu____69325 =
                                       FStar_Syntax_Print.comp_to_string c2
                                        in
                                     let uu____69327 =
                                       FStar_Syntax_Print.term_to_string t2
                                        in
                                     let uu____69329 =
                                       FStar_Extraction_ML_Code.string_of_mlty
                                         env1.FStar_Extraction_ML_UEnv.currentModule
                                         res
                                        in
                                     FStar_Util.print3
                                       "Translated comp type %s as %s ... to %s\n"
                                       uu____69325 uu____69327 uu____69329);
                                res))
                            else
                              translate_term_to_mlty env1
                                (FStar_Syntax_Util.comp_result c2)
                         in
                      let erase =
                        effect_as_etag env1
                          (FStar_Syntax_Util.comp_effect_name c1)
                         in
                      let uu____69335 =
                        FStar_List.fold_right
                          (fun uu____69355  ->
                             fun uu____69356  ->
                               match (uu____69355, uu____69356) with
                               | ((uu____69379,t2),(tag,t')) ->
                                   (FStar_Extraction_ML_Syntax.E_PURE,
                                     (FStar_Extraction_ML_Syntax.MLTY_Fun
                                        (t2, tag, t')))) mlbs (erase, t_ret)
                         in
                      (match uu____69335 with | (uu____69394,t2) -> t2)))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let res =
              let uu____69423 =
                let uu____69424 = FStar_Syntax_Util.un_uinst head1  in
                uu____69424.FStar_Syntax_Syntax.n  in
              match uu____69423 with
              | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv args
              | FStar_Syntax_Syntax.Tm_app (head2,args') ->
                  let uu____69455 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_app
                         (head2, (FStar_List.append args' args)))
                      FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                     in
                  translate_term_to_mlty env uu____69455
              | uu____69476 -> FStar_Extraction_ML_UEnv.unknownType  in
            res
        | FStar_Syntax_Syntax.Tm_abs (bs,ty,uu____69479) ->
            let uu____69504 = FStar_Syntax_Subst.open_term bs ty  in
            (match uu____69504 with
             | (bs1,ty1) ->
                 let uu____69511 = binders_as_ml_binders env bs1  in
                 (match uu____69511 with
                  | (bts,env1) -> translate_term_to_mlty env1 ty1))
        | FStar_Syntax_Syntax.Tm_let uu____69539 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_match uu____69553 ->
            FStar_Extraction_ML_UEnv.unknownType
         in
      let rec is_top_ty t =
        match t with
        | FStar_Extraction_ML_Syntax.MLTY_Top  -> true
        | FStar_Extraction_ML_Syntax.MLTY_Named uu____69585 ->
            let uu____69592 = FStar_Extraction_ML_Util.udelta_unfold g t  in
            (match uu____69592 with
             | FStar_Pervasives_Native.None  -> false
             | FStar_Pervasives_Native.Some t1 -> is_top_ty t1)
        | uu____69598 -> false  in
      let uu____69600 =
        FStar_TypeChecker_Util.must_erase_for_extraction
          g.FStar_Extraction_ML_UEnv.env_tcenv t0
         in
      if uu____69600
      then FStar_Extraction_ML_Syntax.MLTY_Erased
      else
        (let mlt = aux g t0  in
         let uu____69606 = is_top_ty mlt  in
         if uu____69606 then FStar_Extraction_ML_Syntax.MLTY_Top else mlt)

and (binders_as_ml_binders :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.binders ->
      ((FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)
        Prims.list * FStar_Extraction_ML_UEnv.uenv))
  =
  fun g  ->
    fun bs  ->
      let uu____69624 =
        FStar_All.pipe_right bs
          (FStar_List.fold_left
             (fun uu____69680  ->
                fun b  ->
                  match uu____69680 with
                  | (ml_bs,env) ->
                      let uu____69726 = is_type_binder g b  in
                      if uu____69726
                      then
                        let b1 = FStar_Pervasives_Native.fst b  in
                        let env1 =
                          FStar_Extraction_ML_UEnv.extend_ty env b1
                            (FStar_Pervasives_Native.Some
                               FStar_Extraction_ML_Syntax.MLTY_Top)
                           in
                        let ml_b =
                          let uu____69752 =
                            FStar_Extraction_ML_UEnv.bv_as_ml_termvar b1  in
                          (uu____69752,
                            FStar_Extraction_ML_Syntax.ml_unit_ty)
                           in
                        ((ml_b :: ml_bs), env1)
                      else
                        (let b1 = FStar_Pervasives_Native.fst b  in
                         let t =
                           translate_term_to_mlty env
                             b1.FStar_Syntax_Syntax.sort
                            in
                         let uu____69773 =
                           FStar_Extraction_ML_UEnv.extend_bv env b1 
                             ([], t) false false false
                            in
                         match uu____69773 with
                         | (env1,b2,uu____69798) ->
                             let ml_b =
                               let uu____69807 =
                                 FStar_Extraction_ML_UEnv.removeTick b2  in
                               (uu____69807, t)  in
                             ((ml_b :: ml_bs), env1))) ([], g))
         in
      match uu____69624 with | (ml_bs,env) -> ((FStar_List.rev ml_bs), env)

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
      | (FStar_Extraction_ML_Syntax.MLE_Seq es1,uu____69903) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (FStar_List.append es1 [e2])
      | (uu____69906,FStar_Extraction_ML_Syntax.MLE_Seq es2) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (e1 :: es2)
      | uu____69910 -> FStar_Extraction_ML_Syntax.MLE_Seq [e1; e2]
  
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
                    | uu____69944 when
                        (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
                          =
                          FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr
                        -> body.FStar_Extraction_ML_Syntax.expr
                    | uu____69945 ->
                        mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def
                          body)
             | uu____69946 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body))
        | uu____69955 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body)
  
let (resugar_pat :
  FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option ->
    FStar_Extraction_ML_Syntax.mlpattern ->
      FStar_Extraction_ML_Syntax.mlpattern)
  =
  fun q  ->
    fun p  ->
      match p with
      | FStar_Extraction_ML_Syntax.MLP_CTor (d,pats) ->
          let uu____69983 = FStar_Extraction_ML_Util.is_xtuple d  in
          (match uu____69983 with
           | FStar_Pervasives_Native.Some n1 ->
               FStar_Extraction_ML_Syntax.MLP_Tuple pats
           | uu____69990 ->
               (match q with
                | FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Record_ctor (ty,fns)) ->
                    let path =
                      FStar_List.map FStar_Ident.text_of_id ty.FStar_Ident.ns
                       in
                    let fs = record_fields fns pats  in
                    FStar_Extraction_ML_Syntax.MLP_Record (path, fs)
                | uu____70023 -> p))
      | uu____70026 -> p
  
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
                       (fun uu____70128  ->
                          let uu____70129 =
                            FStar_Extraction_ML_Code.string_of_mlty
                              g.FStar_Extraction_ML_UEnv.currentModule t'
                             in
                          let uu____70131 =
                            FStar_Extraction_ML_Code.string_of_mlty
                              g.FStar_Extraction_ML_UEnv.currentModule t
                             in
                          FStar_Util.print2
                            "Expected pattern type %s; got pattern type %s\n"
                            uu____70129 uu____70131)
                   else ();
                   ok)
               in
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int
                (c,swopt)) when
                let uu____70167 = FStar_Options.codegen ()  in
                uu____70167 <>
                  (FStar_Pervasives_Native.Some FStar_Options.Kremlin)
                ->
                let uu____70172 =
                  match swopt with
                  | FStar_Pervasives_Native.None  ->
                      let uu____70185 =
                        let uu____70186 =
                          let uu____70187 =
                            FStar_Extraction_ML_Util.mlconst_of_const
                              p.FStar_Syntax_Syntax.p
                              (FStar_Const.Const_int
                                 (c, FStar_Pervasives_Native.None))
                             in
                          FStar_Extraction_ML_Syntax.MLE_Const uu____70187
                           in
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.ml_int_ty)
                          uu____70186
                         in
                      (uu____70185, FStar_Extraction_ML_Syntax.ml_int_ty)
                  | FStar_Pervasives_Native.Some sw ->
                      let source_term =
                        FStar_ToSyntax_ToSyntax.desugar_machine_integer
                          (g.FStar_Extraction_ML_UEnv.env_tcenv).FStar_TypeChecker_Env.dsenv
                          c sw FStar_Range.dummyRange
                         in
                      let uu____70209 = term_as_mlexpr g source_term  in
                      (match uu____70209 with
                       | (mlterm,uu____70221,mlty) -> (mlterm, mlty))
                   in
                (match uu____70172 with
                 | (mlc,ml_ty) ->
                     let x = FStar_Extraction_ML_Syntax.gensym ()  in
                     let when_clause =
                       let uu____70243 =
                         let uu____70244 =
                           let uu____70251 =
                             let uu____70254 =
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty ml_ty)
                                 (FStar_Extraction_ML_Syntax.MLE_Var x)
                                in
                             [uu____70254; mlc]  in
                           (FStar_Extraction_ML_Util.prims_op_equality,
                             uu____70251)
                            in
                         FStar_Extraction_ML_Syntax.MLE_App uu____70244  in
                       FStar_All.pipe_left
                         (FStar_Extraction_ML_Syntax.with_ty
                            FStar_Extraction_ML_Syntax.ml_bool_ty)
                         uu____70243
                        in
                     let uu____70257 = ok ml_ty  in
                     (g,
                       (FStar_Pervasives_Native.Some
                          ((FStar_Extraction_ML_Syntax.MLP_Var x),
                            [when_clause])), uu____70257))
            | FStar_Syntax_Syntax.Pat_constant s ->
                let t =
                  FStar_TypeChecker_TcTerm.tc_constant
                    g.FStar_Extraction_ML_UEnv.env_tcenv
                    FStar_Range.dummyRange s
                   in
                let mlty = term_as_mlty g t  in
                let uu____70279 =
                  let uu____70288 =
                    let uu____70295 =
                      let uu____70296 =
                        FStar_Extraction_ML_Util.mlconst_of_const
                          p.FStar_Syntax_Syntax.p s
                         in
                      FStar_Extraction_ML_Syntax.MLP_Const uu____70296  in
                    (uu____70295, [])  in
                  FStar_Pervasives_Native.Some uu____70288  in
                let uu____70305 = ok mlty  in (g, uu____70279, uu____70305)
            | FStar_Syntax_Syntax.Pat_var x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort  in
                let uu____70318 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp
                   in
                (match uu____70318 with
                 | (g1,x1,uu____70346) ->
                     let uu____70349 = ok mlty  in
                     (g1,
                       (if imp
                        then FStar_Pervasives_Native.None
                        else
                          FStar_Pervasives_Native.Some
                            ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                       uu____70349))
            | FStar_Syntax_Syntax.Pat_wild x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort  in
                let uu____70387 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp
                   in
                (match uu____70387 with
                 | (g1,x1,uu____70415) ->
                     let uu____70418 = ok mlty  in
                     (g1,
                       (if imp
                        then FStar_Pervasives_Native.None
                        else
                          FStar_Pervasives_Native.Some
                            ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                       uu____70418))
            | FStar_Syntax_Syntax.Pat_dot_term uu____70454 ->
                (g, FStar_Pervasives_Native.None, true)
            | FStar_Syntax_Syntax.Pat_cons (f,pats) ->
                let uu____70497 =
                  let uu____70506 = FStar_Extraction_ML_UEnv.lookup_fv g f
                     in
                  match uu____70506 with
                  | { FStar_Extraction_ML_UEnv.exp_b_name = uu____70515;
                      FStar_Extraction_ML_UEnv.exp_b_expr =
                        {
                          FStar_Extraction_ML_Syntax.expr =
                            FStar_Extraction_ML_Syntax.MLE_Name n1;
                          FStar_Extraction_ML_Syntax.mlty = uu____70517;
                          FStar_Extraction_ML_Syntax.loc = uu____70518;_};
                      FStar_Extraction_ML_UEnv.exp_b_tscheme = ttys;
                      FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____70520;_}
                      -> (n1, ttys)
                  | uu____70527 -> failwith "Expected a constructor"  in
                (match uu____70497 with
                 | (d,tys) ->
                     let nTyVars =
                       FStar_List.length (FStar_Pervasives_Native.fst tys)
                        in
                     let uu____70564 = FStar_Util.first_N nTyVars pats  in
                     (match uu____70564 with
                      | (tysVarPats,restPats) ->
                          let f_ty_opt =
                            try
                              (fun uu___1429_70668  ->
                                 match () with
                                 | () ->
                                     let mlty_args =
                                       FStar_All.pipe_right tysVarPats
                                         (FStar_List.map
                                            (fun uu____70699  ->
                                               match uu____70699 with
                                               | (p1,uu____70706) ->
                                                   (match p1.FStar_Syntax_Syntax.v
                                                    with
                                                    | FStar_Syntax_Syntax.Pat_dot_term
                                                        (uu____70709,t) ->
                                                        term_as_mlty g t
                                                    | uu____70715 ->
                                                        (FStar_Extraction_ML_UEnv.debug
                                                           g
                                                           (fun uu____70719 
                                                              ->
                                                              let uu____70720
                                                                =
                                                                FStar_Syntax_Print.pat_to_string
                                                                  p1
                                                                 in
                                                              FStar_Util.print1
                                                                "Pattern %s is not extractable"
                                                                uu____70720);
                                                         FStar_Exn.raise
                                                           Un_extractable))))
                                        in
                                     let f_ty =
                                       FStar_Extraction_ML_Util.subst tys
                                         mlty_args
                                        in
                                     let uu____70724 =
                                       FStar_Extraction_ML_Util.uncurry_mlty_fun
                                         f_ty
                                        in
                                     FStar_Pervasives_Native.Some uu____70724)
                                ()
                            with
                            | Un_extractable  -> FStar_Pervasives_Native.None
                             in
                          let uu____70753 =
                            FStar_Util.fold_map
                              (fun g1  ->
                                 fun uu____70790  ->
                                   match uu____70790 with
                                   | (p1,imp1) ->
                                       let uu____70812 =
                                         extract_one_pat true g1 p1
                                           FStar_Pervasives_Native.None
                                           term_as_mlexpr
                                          in
                                       (match uu____70812 with
                                        | (g2,p2,uu____70843) -> (g2, p2))) g
                              tysVarPats
                             in
                          (match uu____70753 with
                           | (g1,tyMLPats) ->
                               let uu____70907 =
                                 FStar_Util.fold_map
                                   (fun uu____70972  ->
                                      fun uu____70973  ->
                                        match (uu____70972, uu____70973) with
                                        | ((g2,f_ty_opt1),(p1,imp1)) ->
                                            let uu____71071 =
                                              match f_ty_opt1 with
                                              | FStar_Pervasives_Native.Some
                                                  (hd1::rest,res) ->
                                                  ((FStar_Pervasives_Native.Some
                                                      (rest, res)),
                                                    (FStar_Pervasives_Native.Some
                                                       hd1))
                                              | uu____71131 ->
                                                  (FStar_Pervasives_Native.None,
                                                    FStar_Pervasives_Native.None)
                                               in
                                            (match uu____71071 with
                                             | (f_ty_opt2,expected_ty) ->
                                                 let uu____71202 =
                                                   extract_one_pat false g2
                                                     p1 expected_ty
                                                     term_as_mlexpr
                                                    in
                                                 (match uu____71202 with
                                                  | (g3,p2,uu____71245) ->
                                                      ((g3, f_ty_opt2), p2))))
                                   (g1, f_ty_opt) restPats
                                  in
                               (match uu____70907 with
                                | ((g2,f_ty_opt1),restMLPats) ->
                                    let uu____71366 =
                                      let uu____71377 =
                                        FStar_All.pipe_right
                                          (FStar_List.append tyMLPats
                                             restMLPats)
                                          (FStar_List.collect
                                             (fun uu___618_71428  ->
                                                match uu___618_71428 with
                                                | FStar_Pervasives_Native.Some
                                                    x -> [x]
                                                | uu____71470 -> []))
                                         in
                                      FStar_All.pipe_right uu____71377
                                        FStar_List.split
                                       in
                                    (match uu____71366 with
                                     | (mlPats,when_clauses) ->
                                         let pat_ty_compat =
                                           match f_ty_opt1 with
                                           | FStar_Pervasives_Native.Some
                                               ([],t) -> ok t
                                           | uu____71546 -> false  in
                                         let uu____71556 =
                                           let uu____71565 =
                                             let uu____71572 =
                                               resugar_pat
                                                 f.FStar_Syntax_Syntax.fv_qual
                                                 (FStar_Extraction_ML_Syntax.MLP_CTor
                                                    (d, mlPats))
                                                in
                                             let uu____71575 =
                                               FStar_All.pipe_right
                                                 when_clauses
                                                 FStar_List.flatten
                                                in
                                             (uu____71572, uu____71575)  in
                                           FStar_Pervasives_Native.Some
                                             uu____71565
                                            in
                                         (g2, uu____71556, pat_ty_compat))))))
  
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
            let uu____71707 =
              extract_one_pat false g1 p1 expected_t1 term_as_mlexpr  in
            match uu____71707 with
            | (g2,FStar_Pervasives_Native.Some (x,v1),b) -> (g2, (x, v1), b)
            | uu____71770 ->
                failwith "Impossible: Unable to translate pattern"
             in
          let mk_when_clause whens =
            match whens with
            | [] -> FStar_Pervasives_Native.None
            | hd1::tl1 ->
                let uu____71818 =
                  FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd1
                    tl1
                   in
                FStar_Pervasives_Native.Some uu____71818
             in
          let uu____71819 =
            extract_one_pat1 g p (FStar_Pervasives_Native.Some expected_t)
             in
          match uu____71819 with
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
            | FStar_Extraction_ML_Syntax.MLTY_Fun (t0,uu____71979,t1) ->
                let x = FStar_Extraction_ML_Syntax.gensym ()  in
                let uu____71983 =
                  let uu____71995 =
                    let uu____72005 =
                      FStar_All.pipe_left
                        (FStar_Extraction_ML_Syntax.with_ty t0)
                        (FStar_Extraction_ML_Syntax.MLE_Var x)
                       in
                    ((x, t0), uu____72005)  in
                  uu____71995 :: more_args  in
                eta_args uu____71983 t1
            | FStar_Extraction_ML_Syntax.MLTY_Named (uu____72021,uu____72022)
                -> ((FStar_List.rev more_args), t)
            | uu____72047 ->
                let uu____72048 =
                  let uu____72050 =
                    FStar_Extraction_ML_Code.string_of_mlexpr
                      g.FStar_Extraction_ML_UEnv.currentModule mlAppExpr
                     in
                  let uu____72052 =
                    FStar_Extraction_ML_Code.string_of_mlty
                      g.FStar_Extraction_ML_UEnv.currentModule t
                     in
                  FStar_Util.format2
                    "Impossible: Head type is not an arrow: (%s : %s)"
                    uu____72050 uu____72052
                   in
                failwith uu____72048
             in
          let as_record qual1 e =
            match ((e.FStar_Extraction_ML_Syntax.expr), qual1) with
            | (FStar_Extraction_ML_Syntax.MLE_CTor
               (uu____72087,args),FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Record_ctor (tyname,fields))) ->
                let path =
                  FStar_List.map FStar_Ident.text_of_id tyname.FStar_Ident.ns
                   in
                let fields1 = record_fields fields args  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     e.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_Record (path, fields1))
            | uu____72124 -> e  in
          let resugar_and_maybe_eta qual1 e =
            let uu____72146 = eta_args [] residualType  in
            match uu____72146 with
            | (eargs,tres) ->
                (match eargs with
                 | [] ->
                     let uu____72204 = as_record qual1 e  in
                     FStar_Extraction_ML_Util.resugar_exp uu____72204
                 | uu____72205 ->
                     let uu____72217 = FStar_List.unzip eargs  in
                     (match uu____72217 with
                      | (binders,eargs1) ->
                          (match e.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_CTor (head1,args)
                               ->
                               let body =
                                 let uu____72263 =
                                   let uu____72264 =
                                     FStar_All.pipe_left
                                       (FStar_Extraction_ML_Syntax.with_ty
                                          tres)
                                       (FStar_Extraction_ML_Syntax.MLE_CTor
                                          (head1,
                                            (FStar_List.append args eargs1)))
                                      in
                                   FStar_All.pipe_left (as_record qual1)
                                     uu____72264
                                    in
                                 FStar_All.pipe_left
                                   FStar_Extraction_ML_Util.resugar_exp
                                   uu____72263
                                  in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    e.FStar_Extraction_ML_Syntax.mlty)
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    (binders, body))
                           | uu____72274 ->
                               failwith "Impossible: Not a constructor")))
             in
          match ((mlAppExpr.FStar_Extraction_ML_Syntax.expr), qual) with
          | (uu____72278,FStar_Pervasives_Native.None ) -> mlAppExpr
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____72282;
                FStar_Extraction_ML_Syntax.loc = uu____72283;_},mle::args),FStar_Pervasives_Native.Some
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
                | uu____72306 ->
                    let uu____72309 =
                      let uu____72316 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj
                         in
                      (uu____72316, args)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____72309
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
                     FStar_Extraction_ML_Syntax.mlty = uu____72320;
                     FStar_Extraction_ML_Syntax.loc = uu____72321;_},uu____72322);
                FStar_Extraction_ML_Syntax.mlty = uu____72323;
                FStar_Extraction_ML_Syntax.loc = uu____72324;_},mle::args),FStar_Pervasives_Native.Some
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
                | uu____72351 ->
                    let uu____72354 =
                      let uu____72361 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj
                         in
                      (uu____72361, args)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____72354
                 in
              FStar_Extraction_ML_Syntax.with_ty
                mlAppExpr.FStar_Extraction_ML_Syntax.mlty e
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____72365;
                FStar_Extraction_ML_Syntax.loc = uu____72366;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____72374 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____72374
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____72378;
                FStar_Extraction_ML_Syntax.loc = uu____72379;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____72381)) ->
              let uu____72394 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____72394
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____72398;
                     FStar_Extraction_ML_Syntax.loc = uu____72399;_},uu____72400);
                FStar_Extraction_ML_Syntax.mlty = uu____72401;
                FStar_Extraction_ML_Syntax.loc = uu____72402;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____72414 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____72414
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____72418;
                     FStar_Extraction_ML_Syntax.loc = uu____72419;_},uu____72420);
                FStar_Extraction_ML_Syntax.mlty = uu____72421;
                FStar_Extraction_ML_Syntax.loc = uu____72422;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____72424)) ->
              let uu____72441 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____72441
          | (FStar_Extraction_ML_Syntax.MLE_Name
             mlp,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor
             )) ->
              let uu____72447 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____72447
          | (FStar_Extraction_ML_Syntax.MLE_Name
             mlp,FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____72451)) ->
              let uu____72460 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____72460
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____72464;
                FStar_Extraction_ML_Syntax.loc = uu____72465;_},uu____72466),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____72473 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____72473
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____72477;
                FStar_Extraction_ML_Syntax.loc = uu____72478;_},uu____72479),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____72480)) ->
              let uu____72493 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____72493
          | uu____72496 -> mlAppExpr
  
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
        | uu____72527 -> (ml_e, tag)
  
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
      let maybe_generalize uu____72588 =
        match uu____72588 with
        | { FStar_Syntax_Syntax.lbname = lbname_;
            FStar_Syntax_Syntax.lbunivs = uu____72609;
            FStar_Syntax_Syntax.lbtyp = lbtyp;
            FStar_Syntax_Syntax.lbeff = lbeff;
            FStar_Syntax_Syntax.lbdef = lbdef;
            FStar_Syntax_Syntax.lbattrs = uu____72613;
            FStar_Syntax_Syntax.lbpos = uu____72614;_} ->
            let f_e = effect_as_etag g lbeff  in
            let lbtyp1 = FStar_Syntax_Subst.compress lbtyp  in
            let no_gen uu____72695 =
              let expected_t = term_as_mlty g lbtyp1  in
              (lbname_, f_e, (lbtyp1, ([], ([], expected_t))), false, lbdef)
               in
            let uu____72772 =
              FStar_TypeChecker_Util.must_erase_for_extraction
                g.FStar_Extraction_ML_UEnv.env_tcenv lbtyp1
               in
            if uu____72772
            then
              (lbname_, f_e,
                (lbtyp1, ([], ([], FStar_Extraction_ML_Syntax.MLTY_Erased))),
                false, lbdef)
            else
              (match lbtyp1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                   let uu____72858 = FStar_List.hd bs  in
                   FStar_All.pipe_right uu____72858 (is_type_binder g) ->
                   let uu____72880 = FStar_Syntax_Subst.open_comp bs c  in
                   (match uu____72880 with
                    | (bs1,c1) ->
                        let uu____72906 =
                          let uu____72919 =
                            FStar_Util.prefix_until
                              (fun x  ->
                                 let uu____72965 = is_type_binder g x  in
                                 Prims.op_Negation uu____72965) bs1
                             in
                          match uu____72919 with
                          | FStar_Pervasives_Native.None  ->
                              (bs1, (FStar_Syntax_Util.comp_result c1))
                          | FStar_Pervasives_Native.Some (bs2,b,rest) ->
                              let uu____73092 =
                                FStar_Syntax_Util.arrow (b :: rest) c1  in
                              (bs2, uu____73092)
                           in
                        (match uu____72906 with
                         | (tbinders,tbody) ->
                             let n_tbinders = FStar_List.length tbinders  in
                             let lbdef1 =
                               let uu____73154 = normalize_abs lbdef  in
                               FStar_All.pipe_right uu____73154
                                 FStar_Syntax_Util.unmeta
                                in
                             (match lbdef1.FStar_Syntax_Syntax.n with
                              | FStar_Syntax_Syntax.Tm_abs (bs2,body,copt) ->
                                  let uu____73203 =
                                    FStar_Syntax_Subst.open_term bs2 body  in
                                  (match uu____73203 with
                                   | (bs3,body1) ->
                                       if
                                         n_tbinders <=
                                           (FStar_List.length bs3)
                                       then
                                         let uu____73255 =
                                           FStar_Util.first_N n_tbinders bs3
                                            in
                                         (match uu____73255 with
                                          | (targs,rest_args) ->
                                              let expected_source_ty =
                                                let s =
                                                  FStar_List.map2
                                                    (fun uu____73358  ->
                                                       fun uu____73359  ->
                                                         match (uu____73358,
                                                                 uu____73359)
                                                         with
                                                         | ((x,uu____73385),
                                                            (y,uu____73387))
                                                             ->
                                                             let uu____73408
                                                               =
                                                               let uu____73415
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   y
                                                                  in
                                                               (x,
                                                                 uu____73415)
                                                                in
                                                             FStar_Syntax_Syntax.NT
                                                               uu____73408)
                                                    tbinders targs
                                                   in
                                                FStar_Syntax_Subst.subst s
                                                  tbody
                                                 in
                                              let env =
                                                FStar_List.fold_left
                                                  (fun env  ->
                                                     fun uu____73432  ->
                                                       match uu____73432 with
                                                       | (a,uu____73440) ->
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
                                                let uu____73451 =
                                                  FStar_All.pipe_right targs
                                                    (FStar_List.map
                                                       (fun uu____73470  ->
                                                          match uu____73470
                                                          with
                                                          | (x,uu____73479)
                                                              ->
                                                              FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                                x))
                                                   in
                                                (uu____73451, expected_t)  in
                                              let add_unit =
                                                match rest_args with
                                                | [] ->
                                                    (let uu____73495 =
                                                       is_fstar_value body1
                                                        in
                                                     Prims.op_Negation
                                                       uu____73495)
                                                      ||
                                                      (let uu____73498 =
                                                         FStar_Syntax_Util.is_pure_comp
                                                           c1
                                                          in
                                                       Prims.op_Negation
                                                         uu____73498)
                                                | uu____73500 -> false  in
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
                              | FStar_Syntax_Syntax.Tm_uinst uu____73562 ->
                                  let env =
                                    FStar_List.fold_left
                                      (fun env  ->
                                         fun uu____73581  ->
                                           match uu____73581 with
                                           | (a,uu____73589) ->
                                               FStar_Extraction_ML_UEnv.extend_ty
                                                 env a
                                                 FStar_Pervasives_Native.None)
                                      g tbinders
                                     in
                                  let expected_t = term_as_mlty env tbody  in
                                  let polytype =
                                    let uu____73600 =
                                      FStar_All.pipe_right tbinders
                                        (FStar_List.map
                                           (fun uu____73619  ->
                                              match uu____73619 with
                                              | (x,uu____73628) ->
                                                  FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                    x))
                                       in
                                    (uu____73600, expected_t)  in
                                  let args =
                                    FStar_All.pipe_right tbinders
                                      (FStar_List.map
                                         (fun uu____73672  ->
                                            match uu____73672 with
                                            | (bv,uu____73680) ->
                                                let uu____73685 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    bv
                                                   in
                                                FStar_All.pipe_right
                                                  uu____73685
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
                              | FStar_Syntax_Syntax.Tm_fvar uu____73715 ->
                                  let env =
                                    FStar_List.fold_left
                                      (fun env  ->
                                         fun uu____73728  ->
                                           match uu____73728 with
                                           | (a,uu____73736) ->
                                               FStar_Extraction_ML_UEnv.extend_ty
                                                 env a
                                                 FStar_Pervasives_Native.None)
                                      g tbinders
                                     in
                                  let expected_t = term_as_mlty env tbody  in
                                  let polytype =
                                    let uu____73747 =
                                      FStar_All.pipe_right tbinders
                                        (FStar_List.map
                                           (fun uu____73766  ->
                                              match uu____73766 with
                                              | (x,uu____73775) ->
                                                  FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                    x))
                                       in
                                    (uu____73747, expected_t)  in
                                  let args =
                                    FStar_All.pipe_right tbinders
                                      (FStar_List.map
                                         (fun uu____73819  ->
                                            match uu____73819 with
                                            | (bv,uu____73827) ->
                                                let uu____73832 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    bv
                                                   in
                                                FStar_All.pipe_right
                                                  uu____73832
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
                              | FStar_Syntax_Syntax.Tm_name uu____73862 ->
                                  let env =
                                    FStar_List.fold_left
                                      (fun env  ->
                                         fun uu____73875  ->
                                           match uu____73875 with
                                           | (a,uu____73883) ->
                                               FStar_Extraction_ML_UEnv.extend_ty
                                                 env a
                                                 FStar_Pervasives_Native.None)
                                      g tbinders
                                     in
                                  let expected_t = term_as_mlty env tbody  in
                                  let polytype =
                                    let uu____73894 =
                                      FStar_All.pipe_right tbinders
                                        (FStar_List.map
                                           (fun uu____73913  ->
                                              match uu____73913 with
                                              | (x,uu____73922) ->
                                                  FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                    x))
                                       in
                                    (uu____73894, expected_t)  in
                                  let args =
                                    FStar_All.pipe_right tbinders
                                      (FStar_List.map
                                         (fun uu____73966  ->
                                            match uu____73966 with
                                            | (bv,uu____73974) ->
                                                let uu____73979 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    bv
                                                   in
                                                FStar_All.pipe_right
                                                  uu____73979
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
                              | uu____74009 -> err_value_restriction lbdef1)))
               | uu____74029 -> no_gen ())
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
           fun uu____74180  ->
             match uu____74180 with
             | (lbname,e_tag,(typ,(binders,mltyscheme)),add_unit,_body) ->
                 let uu____74241 =
                   FStar_Extraction_ML_UEnv.extend_lb env lbname typ
                     mltyscheme add_unit is_rec
                    in
                 (match uu____74241 with
                  | (env1,uu____74258,exp_binding) ->
                      let uu____74262 =
                        let uu____74267 = FStar_Util.right lbname  in
                        (uu____74267, exp_binding)  in
                      (env1, uu____74262))) g lbs1
  
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
            (fun uu____74333  ->
               let uu____74334 = FStar_Syntax_Print.term_to_string e  in
               let uu____74336 =
                 FStar_Extraction_ML_Code.string_of_mlty
                   g.FStar_Extraction_ML_UEnv.currentModule ty
                  in
               FStar_Util.print2 "Checking %s at type %s\n" uu____74334
                 uu____74336);
          (match (f, ty) with
           | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____74343) ->
               (FStar_Extraction_ML_Syntax.ml_unit,
                 FStar_Extraction_ML_Syntax.MLTY_Erased)
           | (FStar_Extraction_ML_Syntax.E_PURE
              ,FStar_Extraction_ML_Syntax.MLTY_Erased ) ->
               (FStar_Extraction_ML_Syntax.ml_unit,
                 FStar_Extraction_ML_Syntax.MLTY_Erased)
           | uu____74344 ->
               let uu____74349 = term_as_mlexpr g e  in
               (match uu____74349 with
                | (ml_e,tag,t) ->
                    let uu____74363 = maybe_promote_effect ml_e tag t  in
                    (match uu____74363 with
                     | (ml_e1,tag1) ->
                         let uu____74374 =
                           FStar_Extraction_ML_Util.eff_leq tag1 f  in
                         if uu____74374
                         then
                           let uu____74381 =
                             maybe_coerce e.FStar_Syntax_Syntax.pos g ml_e1 t
                               ty
                              in
                           (uu____74381, ty)
                         else
                           (match (tag1, f, ty) with
                            | (FStar_Extraction_ML_Syntax.E_GHOST
                               ,FStar_Extraction_ML_Syntax.E_PURE
                               ,FStar_Extraction_ML_Syntax.MLTY_Erased ) ->
                                let uu____74388 =
                                  maybe_coerce e.FStar_Syntax_Syntax.pos g
                                    ml_e1 t ty
                                   in
                                (uu____74388, ty)
                            | uu____74389 ->
                                (err_unexpected_eff g e ty f tag1;
                                 (let uu____74397 =
                                    maybe_coerce e.FStar_Syntax_Syntax.pos g
                                      ml_e1 t ty
                                     in
                                  (uu____74397, ty)))))))

and (term_as_mlexpr :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag *
        FStar_Extraction_ML_Syntax.mlty))
  =
  fun g  ->
    fun e  ->
      let uu____74400 = term_as_mlexpr' g e  in
      match uu____74400 with
      | (e1,f,t) ->
          let uu____74416 = maybe_promote_effect e1 f t  in
          (match uu____74416 with | (e2,f1) -> (e2, f1, t))

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
           let uu____74441 =
             let uu____74443 =
               FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos  in
             let uu____74445 = FStar_Syntax_Print.tag_of_term top  in
             let uu____74447 = FStar_Syntax_Print.term_to_string top  in
             FStar_Util.format3 "%s: term_as_mlexpr' (%s) :  %s \n"
               uu____74443 uu____74445 uu____74447
              in
           FStar_Util.print_string uu____74441);
      (let t = FStar_Syntax_Subst.compress top  in
       match t.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____74457 =
             let uu____74459 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____74459
              in
           failwith uu____74457
       | FStar_Syntax_Syntax.Tm_delayed uu____74468 ->
           let uu____74491 =
             let uu____74493 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____74493
              in
           failwith uu____74491
       | FStar_Syntax_Syntax.Tm_uvar uu____74502 ->
           let uu____74515 =
             let uu____74517 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____74517
              in
           failwith uu____74515
       | FStar_Syntax_Syntax.Tm_bvar uu____74526 ->
           let uu____74527 =
             let uu____74529 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____74529
              in
           failwith uu____74527
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____74539 = FStar_Syntax_Util.unfold_lazy i  in
           term_as_mlexpr g uu____74539
       | FStar_Syntax_Syntax.Tm_type uu____74540 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_refine uu____74541 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_arrow uu____74548 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_quoted
           (qt,{
                 FStar_Syntax_Syntax.qkind =
                   FStar_Syntax_Syntax.Quote_dynamic ;
                 FStar_Syntax_Syntax.antiquotes = uu____74564;_})
           ->
           let uu____74577 =
             let uu____74578 =
               FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.failwith_lid
                 FStar_Syntax_Syntax.delta_constant
                 FStar_Pervasives_Native.None
                in
             FStar_Extraction_ML_UEnv.lookup_fv g uu____74578  in
           (match uu____74577 with
            | { FStar_Extraction_ML_UEnv.exp_b_name = uu____74585;
                FStar_Extraction_ML_UEnv.exp_b_expr = fw;
                FStar_Extraction_ML_UEnv.exp_b_tscheme = uu____74587;
                FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____74588;_} ->
                let uu____74591 =
                  let uu____74592 =
                    let uu____74593 =
                      let uu____74600 =
                        let uu____74603 =
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty
                               FStar_Extraction_ML_Syntax.ml_string_ty)
                            (FStar_Extraction_ML_Syntax.MLE_Const
                               (FStar_Extraction_ML_Syntax.MLC_String
                                  "Cannot evaluate open quotation at runtime"))
                           in
                        [uu____74603]  in
                      (fw, uu____74600)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____74593  in
                  FStar_All.pipe_left
                    (FStar_Extraction_ML_Syntax.with_ty
                       FStar_Extraction_ML_Syntax.ml_int_ty) uu____74592
                   in
                (uu____74591, FStar_Extraction_ML_Syntax.E_PURE,
                  FStar_Extraction_ML_Syntax.ml_int_ty))
       | FStar_Syntax_Syntax.Tm_quoted
           (qt,{
                 FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static ;
                 FStar_Syntax_Syntax.antiquotes = aqs;_})
           ->
           let uu____74621 = FStar_Reflection_Basic.inspect_ln qt  in
           (match uu____74621 with
            | FStar_Reflection_Data.Tv_Var bv ->
                let uu____74629 = FStar_Syntax_Syntax.lookup_aq bv aqs  in
                (match uu____74629 with
                 | FStar_Pervasives_Native.Some tm -> term_as_mlexpr g tm
                 | FStar_Pervasives_Native.None  ->
                     let tv =
                       let uu____74640 =
                         let uu____74647 =
                           FStar_Reflection_Embeddings.e_term_view_aq aqs  in
                         FStar_Syntax_Embeddings.embed uu____74647
                           (FStar_Reflection_Data.Tv_Var bv)
                          in
                       uu____74640 t.FStar_Syntax_Syntax.pos
                         FStar_Pervasives_Native.None
                         FStar_Syntax_Embeddings.id_norm_cb
                        in
                     let t1 =
                       let uu____74655 =
                         let uu____74666 = FStar_Syntax_Syntax.as_arg tv  in
                         [uu____74666]  in
                       FStar_Syntax_Util.mk_app
                         (FStar_Reflection_Data.refl_constant_term
                            FStar_Reflection_Data.fstar_refl_pack_ln)
                         uu____74655
                        in
                     term_as_mlexpr g t1)
            | tv ->
                let tv1 =
                  let uu____74693 =
                    let uu____74700 =
                      FStar_Reflection_Embeddings.e_term_view_aq aqs  in
                    FStar_Syntax_Embeddings.embed uu____74700 tv  in
                  uu____74693 t.FStar_Syntax_Syntax.pos
                    FStar_Pervasives_Native.None
                    FStar_Syntax_Embeddings.id_norm_cb
                   in
                let t1 =
                  let uu____74708 =
                    let uu____74719 = FStar_Syntax_Syntax.as_arg tv1  in
                    [uu____74719]  in
                  FStar_Syntax_Util.mk_app
                    (FStar_Reflection_Data.refl_constant_term
                       FStar_Reflection_Data.fstar_refl_pack_ln) uu____74708
                   in
                term_as_mlexpr g t1)
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_monadic (m,uu____74746)) ->
           let t2 = FStar_Syntax_Subst.compress t1  in
           (match t2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) when
                FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname ->
                let uu____74779 =
                  let uu____74786 =
                    FStar_TypeChecker_Env.effect_decl_opt
                      g.FStar_Extraction_ML_UEnv.env_tcenv m
                     in
                  FStar_Util.must uu____74786  in
                (match uu____74779 with
                 | (ed,qualifiers) ->
                     let uu____74813 =
                       let uu____74815 =
                         FStar_TypeChecker_Env.is_reifiable_effect
                           g.FStar_Extraction_ML_UEnv.env_tcenv
                           ed.FStar_Syntax_Syntax.mname
                          in
                       Prims.op_Negation uu____74815  in
                     if uu____74813
                     then term_as_mlexpr g t2
                     else
                       failwith
                         "This should not happen (should have been handled at Tm_abs level)")
            | uu____74833 -> term_as_mlexpr g t2)
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____74835) -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____74841) -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____74847 =
             FStar_TypeChecker_TcTerm.type_of_tot_term
               g.FStar_Extraction_ML_UEnv.env_tcenv t
              in
           (match uu____74847 with
            | (uu____74860,ty,uu____74862) ->
                let ml_ty = term_as_mlty g ty  in
                let uu____74864 =
                  let uu____74865 =
                    FStar_Extraction_ML_Util.mlexpr_of_const
                      t.FStar_Syntax_Syntax.pos c
                     in
                  FStar_Extraction_ML_Syntax.with_ty ml_ty uu____74865  in
                (uu____74864, FStar_Extraction_ML_Syntax.E_PURE, ml_ty))
       | FStar_Syntax_Syntax.Tm_name uu____74866 ->
           let uu____74867 = is_type g t  in
           if uu____74867
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____74878 = FStar_Extraction_ML_UEnv.lookup_term g t  in
              match uu____74878 with
              | (FStar_Util.Inl uu____74891,uu____74892) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | (FStar_Util.Inr
                 { FStar_Extraction_ML_UEnv.exp_b_name = uu____74897;
                   FStar_Extraction_ML_UEnv.exp_b_expr = x;
                   FStar_Extraction_ML_UEnv.exp_b_tscheme = mltys;
                   FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____74900;_},qual)
                  ->
                  (match mltys with
                   | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                       ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | ([],t1) ->
                       let uu____74918 =
                         maybe_eta_data_and_project_record g qual t1 x  in
                       (uu____74918, FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | uu____74919 -> err_uninst g t mltys t))
       | FStar_Syntax_Syntax.Tm_fvar fv ->
           let uu____74927 = is_type g t  in
           if uu____74927
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____74938 = FStar_Extraction_ML_UEnv.try_lookup_fv g fv
                 in
              match uu____74938 with
              | FStar_Pervasives_Native.None  ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.MLTY_Erased)
              | FStar_Pervasives_Native.Some
                  { FStar_Extraction_ML_UEnv.exp_b_name = uu____74947;
                    FStar_Extraction_ML_UEnv.exp_b_expr = x;
                    FStar_Extraction_ML_UEnv.exp_b_tscheme = mltys;
                    FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____74950;_}
                  ->
                  (FStar_Extraction_ML_UEnv.debug g
                     (fun uu____74958  ->
                        let uu____74959 = FStar_Syntax_Print.fv_to_string fv
                           in
                        let uu____74961 =
                          FStar_Extraction_ML_Code.string_of_mlexpr
                            g.FStar_Extraction_ML_UEnv.currentModule x
                           in
                        let uu____74963 =
                          FStar_Extraction_ML_Code.string_of_mlty
                            g.FStar_Extraction_ML_UEnv.currentModule
                            (FStar_Pervasives_Native.snd mltys)
                           in
                        FStar_Util.print3 "looked up %s: got %s at %s \n"
                          uu____74959 uu____74961 uu____74963);
                   (match mltys with
                    | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                        ->
                        (FStar_Extraction_ML_Syntax.ml_unit,
                          FStar_Extraction_ML_Syntax.E_PURE, t1)
                    | ([],t1) ->
                        let uu____74976 =
                          maybe_eta_data_and_project_record g
                            fv.FStar_Syntax_Syntax.fv_qual t1 x
                           in
                        (uu____74976, FStar_Extraction_ML_Syntax.E_PURE, t1)
                    | uu____74977 -> err_uninst g t mltys t)))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,rcopt) ->
           let uu____75011 = FStar_Syntax_Subst.open_term bs body  in
           (match uu____75011 with
            | (bs1,body1) ->
                let uu____75024 = binders_as_ml_binders g bs1  in
                (match uu____75024 with
                 | (ml_bs,env) ->
                     let body2 =
                       match rcopt with
                       | FStar_Pervasives_Native.Some rc ->
                           let uu____75060 =
                             FStar_TypeChecker_Env.is_reifiable_rc
                               env.FStar_Extraction_ML_UEnv.env_tcenv rc
                              in
                           if uu____75060
                           then
                             FStar_TypeChecker_Util.reify_body
                               env.FStar_Extraction_ML_UEnv.env_tcenv body1
                           else body1
                       | FStar_Pervasives_Native.None  ->
                           (FStar_Extraction_ML_UEnv.debug g
                              (fun uu____75068  ->
                                 let uu____75069 =
                                   FStar_Syntax_Print.term_to_string body1
                                    in
                                 FStar_Util.print1
                                   "No computation type for: %s\n"
                                   uu____75069);
                            body1)
                        in
                     let uu____75072 = term_as_mlexpr env body2  in
                     (match uu____75072 with
                      | (ml_body,f,t1) ->
                          let uu____75088 =
                            FStar_List.fold_right
                              (fun uu____75108  ->
                                 fun uu____75109  ->
                                   match (uu____75108, uu____75109) with
                                   | ((uu____75132,targ),(f1,t2)) ->
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         (FStar_Extraction_ML_Syntax.MLTY_Fun
                                            (targ, f1, t2)))) ml_bs (f, t1)
                             in
                          (match uu____75088 with
                           | (f1,tfun) ->
                               let uu____75155 =
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty tfun)
                                   (FStar_Extraction_ML_Syntax.MLE_Fun
                                      (ml_bs, ml_body))
                                  in
                               (uu____75155, f1, tfun)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____75163;
              FStar_Syntax_Syntax.vars = uu____75164;_},(a1,uu____75166)::[])
           ->
           let ty =
             let uu____75206 =
               FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid  in
             term_as_mlty g uu____75206  in
           let uu____75207 =
             let uu____75208 =
               FStar_Extraction_ML_Util.mlexpr_of_range
                 a1.FStar_Syntax_Syntax.pos
                in
             FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty)
               uu____75208
              in
           (uu____75207, FStar_Extraction_ML_Syntax.E_PURE, ty)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____75209;
              FStar_Syntax_Syntax.vars = uu____75210;_},(t1,uu____75212)::
            (r,uu____75214)::[])
           -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____75269);
              FStar_Syntax_Syntax.pos = uu____75270;
              FStar_Syntax_Syntax.vars = uu____75271;_},uu____75272)
           -> failwith "Unreachable? Tm_app Const_reflect"
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let is_total rc =
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_Tot_lid)
               ||
               (FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
                  (FStar_List.existsb
                     (fun uu___619_75341  ->
                        match uu___619_75341 with
                        | FStar_Syntax_Syntax.TOTAL  -> true
                        | uu____75344 -> false)))
              in
           let uu____75346 =
             let uu____75351 =
               let uu____75352 = FStar_Syntax_Subst.compress head1  in
               uu____75352.FStar_Syntax_Syntax.n  in
             ((head1.FStar_Syntax_Syntax.n), uu____75351)  in
           (match uu____75346 with
            | (FStar_Syntax_Syntax.Tm_uvar uu____75361,uu____75362) ->
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
            | (uu____75376,FStar_Syntax_Syntax.Tm_abs
               (bs,uu____75378,FStar_Pervasives_Native.Some rc)) when
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
            | (uu____75403,FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_reify )) ->
                let e =
                  let uu____75405 = FStar_List.hd args  in
                  FStar_TypeChecker_Util.reify_body_with_arg
                    g.FStar_Extraction_ML_UEnv.env_tcenv head1 uu____75405
                   in
                let tm =
                  let uu____75417 =
                    let uu____75422 = FStar_TypeChecker_Util.remove_reify e
                       in
                    let uu____75423 = FStar_List.tl args  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____75422 uu____75423  in
                  uu____75417 FStar_Pervasives_Native.None
                    t.FStar_Syntax_Syntax.pos
                   in
                term_as_mlexpr g tm
            | uu____75432 ->
                let rec extract_app is_data uu____75485 uu____75486 restArgs
                  =
                  match (uu____75485, uu____75486) with
                  | ((mlhead,mlargs_f),(f,t1)) ->
                      let mk_head uu____75567 =
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
                         (fun uu____75594  ->
                            let uu____75595 =
                              let uu____75597 = mk_head ()  in
                              FStar_Extraction_ML_Code.string_of_mlexpr
                                g.FStar_Extraction_ML_UEnv.currentModule
                                uu____75597
                               in
                            let uu____75598 =
                              FStar_Extraction_ML_Code.string_of_mlty
                                g.FStar_Extraction_ML_UEnv.currentModule t1
                               in
                            let uu____75600 =
                              match restArgs with
                              | [] -> "none"
                              | (hd1,uu____75611)::uu____75612 ->
                                  FStar_Syntax_Print.term_to_string hd1
                               in
                            FStar_Util.print3
                              "extract_app ml_head=%s type of head = %s, next arg = %s\n"
                              uu____75595 uu____75598 uu____75600);
                       (match (restArgs, t1) with
                        | ([],uu____75646) ->
                            let app =
                              let uu____75662 = mk_head ()  in
                              maybe_eta_data_and_project_record g is_data t1
                                uu____75662
                               in
                            (app, f, t1)
                        | ((arg,uu____75664)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                           (formal_t,f',t2)) when
                            (is_type g arg) &&
                              (type_leq g formal_t
                                 FStar_Extraction_ML_Syntax.ml_unit_ty)
                            ->
                            let uu____75695 =
                              let uu____75700 =
                                FStar_Extraction_ML_Util.join
                                  arg.FStar_Syntax_Syntax.pos f f'
                                 in
                              (uu____75700, t2)  in
                            extract_app is_data
                              (mlhead,
                                ((FStar_Extraction_ML_Syntax.ml_unit,
                                   FStar_Extraction_ML_Syntax.E_PURE) ::
                                mlargs_f)) uu____75695 rest
                        | ((e0,uu____75712)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                           (tExpected,f',t2)) ->
                            let r = e0.FStar_Syntax_Syntax.pos  in
                            let expected_effect =
                              let uu____75745 =
                                (FStar_Options.lax ()) &&
                                  (FStar_TypeChecker_Util.short_circuit_head
                                     head1)
                                 in
                              if uu____75745
                              then FStar_Extraction_ML_Syntax.E_IMPURE
                              else FStar_Extraction_ML_Syntax.E_PURE  in
                            let uu____75750 =
                              check_term_as_mlexpr g e0 expected_effect
                                tExpected
                               in
                            (match uu____75750 with
                             | (e01,tInferred) ->
                                 let uu____75763 =
                                   let uu____75768 =
                                     FStar_Extraction_ML_Util.join_l r
                                       [f; f']
                                      in
                                   (uu____75768, t2)  in
                                 extract_app is_data
                                   (mlhead, ((e01, expected_effect) ::
                                     mlargs_f)) uu____75763 rest)
                        | uu____75779 ->
                            let uu____75792 =
                              FStar_Extraction_ML_Util.udelta_unfold g t1  in
                            (match uu____75792 with
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
                                  | uu____75864 ->
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
                let extract_app_maybe_projector is_data mlhead uu____75935
                  args1 =
                  match uu____75935 with
                  | (f,t1) ->
                      (match is_data with
                       | FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_projector uu____75965)
                           ->
                           let rec remove_implicits args2 f1 t2 =
                             match (args2, t2) with
                             | ((a0,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____76049))::args3,FStar_Extraction_ML_Syntax.MLTY_Fun
                                (uu____76051,f',t3)) ->
                                 let uu____76089 =
                                   FStar_Extraction_ML_Util.join
                                     a0.FStar_Syntax_Syntax.pos f1 f'
                                    in
                                 remove_implicits args3 uu____76089 t3
                             | uu____76090 -> (args2, f1, t2)  in
                           let uu____76115 = remove_implicits args1 f t1  in
                           (match uu____76115 with
                            | (args2,f1,t2) ->
                                extract_app is_data (mlhead, []) (f1, t2)
                                  args2)
                       | uu____76171 ->
                           extract_app is_data (mlhead, []) (f, t1) args1)
                   in
                let extract_app_with_instantiations uu____76195 =
                  let head2 = FStar_Syntax_Util.un_uinst head1  in
                  match head2.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_name uu____76203 ->
                      let uu____76204 =
                        let uu____76225 =
                          FStar_Extraction_ML_UEnv.lookup_term g head2  in
                        match uu____76225 with
                        | (FStar_Util.Inr exp_b,q) ->
                            (FStar_Extraction_ML_UEnv.debug g
                               (fun uu____76264  ->
                                  let uu____76265 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  let uu____76267 =
                                    FStar_Extraction_ML_Code.string_of_mlexpr
                                      g.FStar_Extraction_ML_UEnv.currentModule
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_expr
                                     in
                                  let uu____76269 =
                                    FStar_Extraction_ML_Code.string_of_mlty
                                      g.FStar_Extraction_ML_UEnv.currentModule
                                      (FStar_Pervasives_Native.snd
                                         exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme)
                                     in
                                  let uu____76271 =
                                    FStar_Util.string_of_bool
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok
                                     in
                                  FStar_Util.print4
                                    "@@@looked up %s: got %s at %s (inst_ok=%s)\n"
                                    uu____76265 uu____76267 uu____76269
                                    uu____76271);
                             (((exp_b.FStar_Extraction_ML_UEnv.exp_b_expr),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok)),
                               q))
                        | uu____76298 -> failwith "FIXME Ty"  in
                      (match uu____76204 with
                       | ((head_ml,(vars,t1),inst_ok),qual) ->
                           let has_typ_apps =
                             match args with
                             | (a,uu____76374)::uu____76375 -> is_type g a
                             | uu____76402 -> false  in
                           let uu____76414 =
                             match vars with
                             | uu____76443::uu____76444 when
                                 (Prims.op_Negation has_typ_apps) && inst_ok
                                 -> (head_ml, t1, args)
                             | uu____76458 ->
                                 let n1 = FStar_List.length vars  in
                                 if n1 <= (FStar_List.length args)
                                 then
                                   let uu____76487 =
                                     FStar_Util.first_N n1 args  in
                                   (match uu____76487 with
                                    | (prefix1,rest) ->
                                        let prefixAsMLTypes =
                                          FStar_List.map
                                            (fun uu____76588  ->
                                               match uu____76588 with
                                               | (x,uu____76596) ->
                                                   term_as_mlty g x) prefix1
                                           in
                                        let t2 =
                                          instantiate (vars, t1)
                                            prefixAsMLTypes
                                           in
                                        (FStar_Extraction_ML_UEnv.debug g
                                           (fun uu____76608  ->
                                              let uu____76609 =
                                                FStar_Syntax_Print.term_to_string
                                                  head2
                                                 in
                                              let uu____76611 =
                                                FStar_Syntax_Print.args_to_string
                                                  prefix1
                                                 in
                                              let uu____76613 =
                                                let uu____76615 =
                                                  FStar_List.map
                                                    (FStar_Extraction_ML_Code.string_of_mlty
                                                       g.FStar_Extraction_ML_UEnv.currentModule)
                                                    prefixAsMLTypes
                                                   in
                                                FStar_All.pipe_right
                                                  uu____76615
                                                  (FStar_String.concat ", ")
                                                 in
                                              let uu____76625 =
                                                FStar_Extraction_ML_Code.string_of_mlty
                                                  g.FStar_Extraction_ML_UEnv.currentModule
                                                  t2
                                                 in
                                              FStar_Util.print4
                                                "@@@looked up %s, instantiated with [%s] translated to [%s], got %s\n"
                                                uu____76609 uu____76611
                                                uu____76613 uu____76625);
                                         (let mk_tapp e ty_args =
                                            match ty_args with
                                            | [] -> e
                                            | uu____76643 ->
                                                let uu___2234_76646 = e  in
                                                {
                                                  FStar_Extraction_ML_Syntax.expr
                                                    =
                                                    (FStar_Extraction_ML_Syntax.MLE_TApp
                                                       (e, ty_args));
                                                  FStar_Extraction_ML_Syntax.mlty
                                                    =
                                                    (uu___2234_76646.FStar_Extraction_ML_Syntax.mlty);
                                                  FStar_Extraction_ML_Syntax.loc
                                                    =
                                                    (uu___2234_76646.FStar_Extraction_ML_Syntax.loc)
                                                }
                                             in
                                          let head3 =
                                            match head_ml.FStar_Extraction_ML_Syntax.expr
                                            with
                                            | FStar_Extraction_ML_Syntax.MLE_Name
                                                uu____76650 ->
                                                let uu___2240_76651 =
                                                  mk_tapp head_ml
                                                    prefixAsMLTypes
                                                   in
                                                {
                                                  FStar_Extraction_ML_Syntax.expr
                                                    =
                                                    (uu___2240_76651.FStar_Extraction_ML_Syntax.expr);
                                                  FStar_Extraction_ML_Syntax.mlty
                                                    = t2;
                                                  FStar_Extraction_ML_Syntax.loc
                                                    =
                                                    (uu___2240_76651.FStar_Extraction_ML_Syntax.loc)
                                                }
                                            | FStar_Extraction_ML_Syntax.MLE_Var
                                                uu____76652 ->
                                                let uu___2240_76654 =
                                                  mk_tapp head_ml
                                                    prefixAsMLTypes
                                                   in
                                                {
                                                  FStar_Extraction_ML_Syntax.expr
                                                    =
                                                    (uu___2240_76654.FStar_Extraction_ML_Syntax.expr);
                                                  FStar_Extraction_ML_Syntax.mlty
                                                    = t2;
                                                  FStar_Extraction_ML_Syntax.loc
                                                    =
                                                    (uu___2240_76654.FStar_Extraction_ML_Syntax.loc)
                                                }
                                            | FStar_Extraction_ML_Syntax.MLE_App
                                                (head3,{
                                                         FStar_Extraction_ML_Syntax.expr
                                                           =
                                                           FStar_Extraction_ML_Syntax.MLE_Const
                                                           (FStar_Extraction_ML_Syntax.MLC_Unit
                                                           );
                                                         FStar_Extraction_ML_Syntax.mlty
                                                           = uu____76656;
                                                         FStar_Extraction_ML_Syntax.loc
                                                           = uu____76657;_}::[])
                                                ->
                                                FStar_All.pipe_right
                                                  (FStar_Extraction_ML_Syntax.MLE_App
                                                     ((let uu___2251_76663 =
                                                         mk_tapp head3
                                                           prefixAsMLTypes
                                                          in
                                                       {
                                                         FStar_Extraction_ML_Syntax.expr
                                                           =
                                                           (uu___2251_76663.FStar_Extraction_ML_Syntax.expr);
                                                         FStar_Extraction_ML_Syntax.mlty
                                                           =
                                                           (FStar_Extraction_ML_Syntax.MLTY_Fun
                                                              (FStar_Extraction_ML_Syntax.ml_unit_ty,
                                                                FStar_Extraction_ML_Syntax.E_PURE,
                                                                t2));
                                                         FStar_Extraction_ML_Syntax.loc
                                                           =
                                                           (uu___2251_76663.FStar_Extraction_ML_Syntax.loc)
                                                       }),
                                                       [FStar_Extraction_ML_Syntax.ml_unit]))
                                                  (FStar_Extraction_ML_Syntax.with_ty
                                                     t2)
                                            | uu____76664 ->
                                                failwith
                                                  "Impossible: Unexpected head term"
                                             in
                                          (head3, t2, rest))))
                                 else err_uninst g head2 (vars, t1) top
                              in
                           (match uu____76414 with
                            | (head_ml1,head_t,args1) ->
                                (match args1 with
                                 | [] ->
                                     let uu____76730 =
                                       maybe_eta_data_and_project_record g
                                         qual head_t head_ml1
                                        in
                                     (uu____76730,
                                       FStar_Extraction_ML_Syntax.E_PURE,
                                       head_t)
                                 | uu____76731 ->
                                     extract_app_maybe_projector qual
                                       head_ml1
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         head_t) args1)))
                  | FStar_Syntax_Syntax.Tm_fvar uu____76740 ->
                      let uu____76741 =
                        let uu____76762 =
                          FStar_Extraction_ML_UEnv.lookup_term g head2  in
                        match uu____76762 with
                        | (FStar_Util.Inr exp_b,q) ->
                            (FStar_Extraction_ML_UEnv.debug g
                               (fun uu____76801  ->
                                  let uu____76802 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  let uu____76804 =
                                    FStar_Extraction_ML_Code.string_of_mlexpr
                                      g.FStar_Extraction_ML_UEnv.currentModule
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_expr
                                     in
                                  let uu____76806 =
                                    FStar_Extraction_ML_Code.string_of_mlty
                                      g.FStar_Extraction_ML_UEnv.currentModule
                                      (FStar_Pervasives_Native.snd
                                         exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme)
                                     in
                                  let uu____76808 =
                                    FStar_Util.string_of_bool
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok
                                     in
                                  FStar_Util.print4
                                    "@@@looked up %s: got %s at %s (inst_ok=%s)\n"
                                    uu____76802 uu____76804 uu____76806
                                    uu____76808);
                             (((exp_b.FStar_Extraction_ML_UEnv.exp_b_expr),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok)),
                               q))
                        | uu____76835 -> failwith "FIXME Ty"  in
                      (match uu____76741 with
                       | ((head_ml,(vars,t1),inst_ok),qual) ->
                           let has_typ_apps =
                             match args with
                             | (a,uu____76911)::uu____76912 -> is_type g a
                             | uu____76939 -> false  in
                           let uu____76951 =
                             match vars with
                             | uu____76980::uu____76981 when
                                 (Prims.op_Negation has_typ_apps) && inst_ok
                                 -> (head_ml, t1, args)
                             | uu____76995 ->
                                 let n1 = FStar_List.length vars  in
                                 if n1 <= (FStar_List.length args)
                                 then
                                   let uu____77024 =
                                     FStar_Util.first_N n1 args  in
                                   (match uu____77024 with
                                    | (prefix1,rest) ->
                                        let prefixAsMLTypes =
                                          FStar_List.map
                                            (fun uu____77125  ->
                                               match uu____77125 with
                                               | (x,uu____77133) ->
                                                   term_as_mlty g x) prefix1
                                           in
                                        let t2 =
                                          instantiate (vars, t1)
                                            prefixAsMLTypes
                                           in
                                        (FStar_Extraction_ML_UEnv.debug g
                                           (fun uu____77145  ->
                                              let uu____77146 =
                                                FStar_Syntax_Print.term_to_string
                                                  head2
                                                 in
                                              let uu____77148 =
                                                FStar_Syntax_Print.args_to_string
                                                  prefix1
                                                 in
                                              let uu____77150 =
                                                let uu____77152 =
                                                  FStar_List.map
                                                    (FStar_Extraction_ML_Code.string_of_mlty
                                                       g.FStar_Extraction_ML_UEnv.currentModule)
                                                    prefixAsMLTypes
                                                   in
                                                FStar_All.pipe_right
                                                  uu____77152
                                                  (FStar_String.concat ", ")
                                                 in
                                              let uu____77162 =
                                                FStar_Extraction_ML_Code.string_of_mlty
                                                  g.FStar_Extraction_ML_UEnv.currentModule
                                                  t2
                                                 in
                                              FStar_Util.print4
                                                "@@@looked up %s, instantiated with [%s] translated to [%s], got %s\n"
                                                uu____77146 uu____77148
                                                uu____77150 uu____77162);
                                         (let mk_tapp e ty_args =
                                            match ty_args with
                                            | [] -> e
                                            | uu____77180 ->
                                                let uu___2234_77183 = e  in
                                                {
                                                  FStar_Extraction_ML_Syntax.expr
                                                    =
                                                    (FStar_Extraction_ML_Syntax.MLE_TApp
                                                       (e, ty_args));
                                                  FStar_Extraction_ML_Syntax.mlty
                                                    =
                                                    (uu___2234_77183.FStar_Extraction_ML_Syntax.mlty);
                                                  FStar_Extraction_ML_Syntax.loc
                                                    =
                                                    (uu___2234_77183.FStar_Extraction_ML_Syntax.loc)
                                                }
                                             in
                                          let head3 =
                                            match head_ml.FStar_Extraction_ML_Syntax.expr
                                            with
                                            | FStar_Extraction_ML_Syntax.MLE_Name
                                                uu____77187 ->
                                                let uu___2240_77188 =
                                                  mk_tapp head_ml
                                                    prefixAsMLTypes
                                                   in
                                                {
                                                  FStar_Extraction_ML_Syntax.expr
                                                    =
                                                    (uu___2240_77188.FStar_Extraction_ML_Syntax.expr);
                                                  FStar_Extraction_ML_Syntax.mlty
                                                    = t2;
                                                  FStar_Extraction_ML_Syntax.loc
                                                    =
                                                    (uu___2240_77188.FStar_Extraction_ML_Syntax.loc)
                                                }
                                            | FStar_Extraction_ML_Syntax.MLE_Var
                                                uu____77189 ->
                                                let uu___2240_77191 =
                                                  mk_tapp head_ml
                                                    prefixAsMLTypes
                                                   in
                                                {
                                                  FStar_Extraction_ML_Syntax.expr
                                                    =
                                                    (uu___2240_77191.FStar_Extraction_ML_Syntax.expr);
                                                  FStar_Extraction_ML_Syntax.mlty
                                                    = t2;
                                                  FStar_Extraction_ML_Syntax.loc
                                                    =
                                                    (uu___2240_77191.FStar_Extraction_ML_Syntax.loc)
                                                }
                                            | FStar_Extraction_ML_Syntax.MLE_App
                                                (head3,{
                                                         FStar_Extraction_ML_Syntax.expr
                                                           =
                                                           FStar_Extraction_ML_Syntax.MLE_Const
                                                           (FStar_Extraction_ML_Syntax.MLC_Unit
                                                           );
                                                         FStar_Extraction_ML_Syntax.mlty
                                                           = uu____77193;
                                                         FStar_Extraction_ML_Syntax.loc
                                                           = uu____77194;_}::[])
                                                ->
                                                FStar_All.pipe_right
                                                  (FStar_Extraction_ML_Syntax.MLE_App
                                                     ((let uu___2251_77200 =
                                                         mk_tapp head3
                                                           prefixAsMLTypes
                                                          in
                                                       {
                                                         FStar_Extraction_ML_Syntax.expr
                                                           =
                                                           (uu___2251_77200.FStar_Extraction_ML_Syntax.expr);
                                                         FStar_Extraction_ML_Syntax.mlty
                                                           =
                                                           (FStar_Extraction_ML_Syntax.MLTY_Fun
                                                              (FStar_Extraction_ML_Syntax.ml_unit_ty,
                                                                FStar_Extraction_ML_Syntax.E_PURE,
                                                                t2));
                                                         FStar_Extraction_ML_Syntax.loc
                                                           =
                                                           (uu___2251_77200.FStar_Extraction_ML_Syntax.loc)
                                                       }),
                                                       [FStar_Extraction_ML_Syntax.ml_unit]))
                                                  (FStar_Extraction_ML_Syntax.with_ty
                                                     t2)
                                            | uu____77201 ->
                                                failwith
                                                  "Impossible: Unexpected head term"
                                             in
                                          (head3, t2, rest))))
                                 else err_uninst g head2 (vars, t1) top
                              in
                           (match uu____76951 with
                            | (head_ml1,head_t,args1) ->
                                (match args1 with
                                 | [] ->
                                     let uu____77267 =
                                       maybe_eta_data_and_project_record g
                                         qual head_t head_ml1
                                        in
                                     (uu____77267,
                                       FStar_Extraction_ML_Syntax.E_PURE,
                                       head_t)
                                 | uu____77268 ->
                                     extract_app_maybe_projector qual
                                       head_ml1
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         head_t) args1)))
                  | uu____77277 ->
                      let uu____77278 = term_as_mlexpr g head2  in
                      (match uu____77278 with
                       | (head3,f,t1) ->
                           extract_app_maybe_projector
                             FStar_Pervasives_Native.None head3 (f, t1) args)
                   in
                let uu____77294 = is_type g t  in
                if uu____77294
                then
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
                else
                  (let uu____77305 =
                     let uu____77306 = FStar_Syntax_Util.un_uinst head1  in
                     uu____77306.FStar_Syntax_Syntax.n  in
                   match uu____77305 with
                   | FStar_Syntax_Syntax.Tm_fvar fv ->
                       let uu____77316 =
                         FStar_Extraction_ML_UEnv.try_lookup_fv g fv  in
                       (match uu____77316 with
                        | FStar_Pervasives_Native.None  ->
                            (FStar_Extraction_ML_Syntax.ml_unit,
                              FStar_Extraction_ML_Syntax.E_PURE,
                              FStar_Extraction_ML_Syntax.MLTY_Erased)
                        | uu____77325 -> extract_app_with_instantiations ())
                   | uu____77328 -> extract_app_with_instantiations ()))
       | FStar_Syntax_Syntax.Tm_ascribed (e0,(tc,uu____77331),f) ->
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
           let uu____77399 = check_term_as_mlexpr g e0 f1 t1  in
           (match uu____77399 with | (e,t2) -> (e, f1, t2))
       | FStar_Syntax_Syntax.Tm_let ((is_rec,lbs),e') ->
           let top_level = FStar_Syntax_Syntax.is_top_level lbs  in
           let uu____77434 =
             if is_rec
             then FStar_Syntax_Subst.open_let_rec lbs e'
             else
               (let uu____77450 = FStar_Syntax_Syntax.is_top_level lbs  in
                if uu____77450
                then (lbs, e')
                else
                  (let lb = FStar_List.hd lbs  in
                   let x =
                     let uu____77465 =
                       FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                     FStar_Syntax_Syntax.freshen_bv uu____77465  in
                   let lb1 =
                     let uu___2302_77467 = lb  in
                     {
                       FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                       FStar_Syntax_Syntax.lbunivs =
                         (uu___2302_77467.FStar_Syntax_Syntax.lbunivs);
                       FStar_Syntax_Syntax.lbtyp =
                         (uu___2302_77467.FStar_Syntax_Syntax.lbtyp);
                       FStar_Syntax_Syntax.lbeff =
                         (uu___2302_77467.FStar_Syntax_Syntax.lbeff);
                       FStar_Syntax_Syntax.lbdef =
                         (uu___2302_77467.FStar_Syntax_Syntax.lbdef);
                       FStar_Syntax_Syntax.lbattrs =
                         (uu___2302_77467.FStar_Syntax_Syntax.lbattrs);
                       FStar_Syntax_Syntax.lbpos =
                         (uu___2302_77467.FStar_Syntax_Syntax.lbpos)
                     }  in
                   let e'1 =
                     FStar_Syntax_Subst.subst
                       [FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x)] e'
                      in
                   ([lb1], e'1)))
              in
           (match uu____77434 with
            | (lbs1,e'1) ->
                let lbs2 =
                  if top_level
                  then
                    FStar_All.pipe_right lbs1
                      (FStar_List.map
                         (fun lb  ->
                            let tcenv =
                              let uu____77501 =
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
                                uu____77501
                               in
                            let lbdef =
                              let uu____77516 = FStar_Options.ml_ish ()  in
                              if uu____77516
                              then lb.FStar_Syntax_Syntax.lbdef
                              else
                                (let norm_call uu____77528 =
                                   FStar_TypeChecker_Normalize.normalize
                                     (FStar_TypeChecker_Env.PureSubtermsWithinComputations
                                     :: extraction_norm_steps) tcenv
                                     lb.FStar_Syntax_Syntax.lbdef
                                    in
                                 let uu____77529 =
                                   (FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug tcenv)
                                      (FStar_Options.Other "Extraction"))
                                     ||
                                     (FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug tcenv)
                                        (FStar_Options.Other "ExtractNorm"))
                                    in
                                 if uu____77529
                                 then
                                   ((let uu____77539 =
                                       FStar_Syntax_Print.lbname_to_string
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     let uu____77541 =
                                       FStar_Syntax_Print.term_to_string
                                         lb.FStar_Syntax_Syntax.lbdef
                                        in
                                     FStar_Util.print2
                                       "Starting to normalize top-level let %s)\n\tlbdef=%s"
                                       uu____77539 uu____77541);
                                    (let a =
                                       let uu____77547 =
                                         let uu____77549 =
                                           FStar_Syntax_Print.lbname_to_string
                                             lb.FStar_Syntax_Syntax.lbname
                                            in
                                         FStar_Util.format1
                                           "###(Time to normalize top-level let %s)"
                                           uu____77549
                                          in
                                       FStar_Util.measure_execution_time
                                         uu____77547 norm_call
                                        in
                                     (let uu____77555 =
                                        FStar_Syntax_Print.term_to_string a
                                         in
                                      FStar_Util.print1 "Normalized to %s\n"
                                        uu____77555);
                                     a))
                                 else norm_call ())
                               in
                            let uu___2320_77560 = lb  in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___2320_77560.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___2320_77560.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp =
                                (uu___2320_77560.FStar_Syntax_Syntax.lbtyp);
                              FStar_Syntax_Syntax.lbeff =
                                (uu___2320_77560.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = lbdef;
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___2320_77560.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___2320_77560.FStar_Syntax_Syntax.lbpos)
                            }))
                  else lbs1  in
                let check_lb env uu____77613 =
                  match uu____77613 with
                  | (nm,(_lbname,f,(_t,(targs,polytype)),add_unit,e)) ->
                      let env1 =
                        FStar_List.fold_left
                          (fun env1  ->
                             fun uu____77769  ->
                               match uu____77769 with
                               | (a,uu____77777) ->
                                   FStar_Extraction_ML_UEnv.extend_ty env1 a
                                     FStar_Pervasives_Native.None) env targs
                         in
                      let expected_t = FStar_Pervasives_Native.snd polytype
                         in
                      let uu____77783 =
                        check_term_as_mlexpr env1 e f expected_t  in
                      (match uu____77783 with
                       | (e1,ty) ->
                           let uu____77794 =
                             maybe_promote_effect e1 f expected_t  in
                           (match uu____77794 with
                            | (e2,f1) ->
                                let meta =
                                  match (f1, ty) with
                                  | (FStar_Extraction_ML_Syntax.E_PURE
                                     ,FStar_Extraction_ML_Syntax.MLTY_Erased
                                     ) -> [FStar_Extraction_ML_Syntax.Erased]
                                  | (FStar_Extraction_ML_Syntax.E_GHOST
                                     ,FStar_Extraction_ML_Syntax.MLTY_Erased
                                     ) -> [FStar_Extraction_ML_Syntax.Erased]
                                  | uu____77806 -> []  in
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
                let uu____77837 =
                  FStar_List.fold_right
                    (fun lb  ->
                       fun uu____77934  ->
                         match uu____77934 with
                         | (env,lbs4) ->
                             let uu____78068 = lb  in
                             (match uu____78068 with
                              | (lbname,uu____78119,(t1,(uu____78121,polytype)),add_unit,uu____78124)
                                  ->
                                  let uu____78139 =
                                    FStar_Extraction_ML_UEnv.extend_lb env
                                      lbname t1 polytype add_unit true
                                     in
                                  (match uu____78139 with
                                   | (env1,nm,uu____78180) ->
                                       (env1, ((nm, lb) :: lbs4))))) lbs3
                    (g, [])
                   in
                (match uu____77837 with
                 | (env_body,lbs4) ->
                     let env_def = if is_rec then env_body else g  in
                     let lbs5 =
                       FStar_All.pipe_right lbs4
                         (FStar_List.map (check_lb env_def))
                        in
                     let e'_rng = e'1.FStar_Syntax_Syntax.pos  in
                     let uu____78459 = term_as_mlexpr env_body e'1  in
                     (match uu____78459 with
                      | (e'2,f',t') ->
                          let f =
                            let uu____78476 =
                              let uu____78479 =
                                FStar_List.map FStar_Pervasives_Native.fst
                                  lbs5
                                 in
                              f' :: uu____78479  in
                            FStar_Extraction_ML_Util.join_l e'_rng
                              uu____78476
                             in
                          let is_rec1 =
                            if is_rec = true
                            then FStar_Extraction_ML_Syntax.Rec
                            else FStar_Extraction_ML_Syntax.NonRec  in
                          let uu____78492 =
                            let uu____78493 =
                              let uu____78494 =
                                let uu____78495 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    lbs5
                                   in
                                (is_rec1, uu____78495)  in
                              mk_MLE_Let top_level uu____78494 e'2  in
                            let uu____78504 =
                              FStar_Extraction_ML_Util.mlloc_of_range
                                t.FStar_Syntax_Syntax.pos
                               in
                            FStar_Extraction_ML_Syntax.with_ty_loc t'
                              uu____78493 uu____78504
                             in
                          (uu____78492, f, t'))))
       | FStar_Syntax_Syntax.Tm_match (scrutinee,pats) ->
           let uu____78543 = term_as_mlexpr g scrutinee  in
           (match uu____78543 with
            | (e,f_e,t_e) ->
                let uu____78559 = check_pats_for_ite pats  in
                (match uu____78559 with
                 | (b,then_e,else_e) ->
                     let no_lift x t1 = x  in
                     if b
                     then
                       (match (then_e, else_e) with
                        | (FStar_Pervasives_Native.Some
                           then_e1,FStar_Pervasives_Native.Some else_e1) ->
                            let uu____78624 = term_as_mlexpr g then_e1  in
                            (match uu____78624 with
                             | (then_mle,f_then,t_then) ->
                                 let uu____78640 = term_as_mlexpr g else_e1
                                    in
                                 (match uu____78640 with
                                  | (else_mle,f_else,t_else) ->
                                      let uu____78656 =
                                        let uu____78667 =
                                          type_leq g t_then t_else  in
                                        if uu____78667
                                        then (t_else, no_lift)
                                        else
                                          (let uu____78688 =
                                             type_leq g t_else t_then  in
                                           if uu____78688
                                           then (t_then, no_lift)
                                           else
                                             (FStar_Extraction_ML_Syntax.MLTY_Top,
                                               FStar_Extraction_ML_Syntax.apply_obj_repr))
                                         in
                                      (match uu____78656 with
                                       | (t_branch,maybe_lift1) ->
                                           let uu____78735 =
                                             let uu____78736 =
                                               let uu____78737 =
                                                 let uu____78746 =
                                                   maybe_lift1 then_mle
                                                     t_then
                                                    in
                                                 let uu____78747 =
                                                   let uu____78750 =
                                                     maybe_lift1 else_mle
                                                       t_else
                                                      in
                                                   FStar_Pervasives_Native.Some
                                                     uu____78750
                                                    in
                                                 (e, uu____78746,
                                                   uu____78747)
                                                  in
                                               FStar_Extraction_ML_Syntax.MLE_If
                                                 uu____78737
                                                in
                                             FStar_All.pipe_left
                                               (FStar_Extraction_ML_Syntax.with_ty
                                                  t_branch) uu____78736
                                              in
                                           let uu____78753 =
                                             FStar_Extraction_ML_Util.join
                                               then_e1.FStar_Syntax_Syntax.pos
                                               f_then f_else
                                              in
                                           (uu____78735, uu____78753,
                                             t_branch))))
                        | uu____78754 ->
                            failwith
                              "ITE pats matched but then and else expressions not found?")
                     else
                       (let uu____78772 =
                          FStar_All.pipe_right pats
                            (FStar_Util.fold_map
                               (fun compat  ->
                                  fun br  ->
                                    let uu____78871 =
                                      FStar_Syntax_Subst.open_branch br  in
                                    match uu____78871 with
                                    | (pat,when_opt,branch1) ->
                                        let uu____78916 =
                                          extract_pat g pat t_e
                                            term_as_mlexpr
                                           in
                                        (match uu____78916 with
                                         | (env,p,pat_t_compat) ->
                                             let uu____78978 =
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
                                                   let uu____79001 =
                                                     term_as_mlexpr env w  in
                                                   (match uu____79001 with
                                                    | (w1,f_w,t_w) ->
                                                        let w2 =
                                                          maybe_coerce w_pos
                                                            env w1 t_w
                                                            FStar_Extraction_ML_Syntax.ml_bool_ty
                                                           in
                                                        ((FStar_Pervasives_Native.Some
                                                            w2), f_w))
                                                in
                                             (match uu____78978 with
                                              | (when_opt1,f_when) ->
                                                  let uu____79051 =
                                                    term_as_mlexpr env
                                                      branch1
                                                     in
                                                  (match uu____79051 with
                                                   | (mlbranch,f_branch,t_branch)
                                                       ->
                                                       let uu____79086 =
                                                         FStar_All.pipe_right
                                                           p
                                                           (FStar_List.map
                                                              (fun
                                                                 uu____79163 
                                                                 ->
                                                                 match uu____79163
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
                                                         uu____79086)))))
                               true)
                           in
                        match uu____78772 with
                        | (pat_t_compat,mlbranches) ->
                            let mlbranches1 = FStar_List.flatten mlbranches
                               in
                            let e1 =
                              if pat_t_compat
                              then e
                              else
                                (FStar_Extraction_ML_UEnv.debug g
                                   (fun uu____79334  ->
                                      let uu____79335 =
                                        FStar_Extraction_ML_Code.string_of_mlexpr
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          e
                                         in
                                      let uu____79337 =
                                        FStar_Extraction_ML_Code.string_of_mlty
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          t_e
                                         in
                                      FStar_Util.print2
                                        "Coercing scrutinee %s from type %s because pattern type is incompatible\n"
                                        uu____79335 uu____79337);
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty t_e)
                                   (FStar_Extraction_ML_Syntax.MLE_Coerce
                                      (e, t_e,
                                        FStar_Extraction_ML_Syntax.MLTY_Top)))
                               in
                            (match mlbranches1 with
                             | [] ->
                                 let uu____79364 =
                                   let uu____79365 =
                                     FStar_Syntax_Syntax.lid_as_fv
                                       FStar_Parser_Const.failwith_lid
                                       FStar_Syntax_Syntax.delta_constant
                                       FStar_Pervasives_Native.None
                                      in
                                   FStar_Extraction_ML_UEnv.lookup_fv g
                                     uu____79365
                                    in
                                 (match uu____79364 with
                                  | {
                                      FStar_Extraction_ML_UEnv.exp_b_name =
                                        uu____79372;
                                      FStar_Extraction_ML_UEnv.exp_b_expr =
                                        fw;
                                      FStar_Extraction_ML_UEnv.exp_b_tscheme
                                        = uu____79374;
                                      FStar_Extraction_ML_UEnv.exp_b_inst_ok
                                        = uu____79375;_}
                                      ->
                                      let uu____79378 =
                                        let uu____79379 =
                                          let uu____79380 =
                                            let uu____79387 =
                                              let uu____79390 =
                                                FStar_All.pipe_left
                                                  (FStar_Extraction_ML_Syntax.with_ty
                                                     FStar_Extraction_ML_Syntax.ml_string_ty)
                                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                                     (FStar_Extraction_ML_Syntax.MLC_String
                                                        "unreachable"))
                                                 in
                                              [uu____79390]  in
                                            (fw, uu____79387)  in
                                          FStar_Extraction_ML_Syntax.MLE_App
                                            uu____79380
                                           in
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             FStar_Extraction_ML_Syntax.ml_int_ty)
                                          uu____79379
                                         in
                                      (uu____79378,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        FStar_Extraction_ML_Syntax.ml_int_ty))
                             | (uu____79394,uu____79395,(uu____79396,f_first,t_first))::rest
                                 ->
                                 let uu____79456 =
                                   FStar_List.fold_left
                                     (fun uu____79498  ->
                                        fun uu____79499  ->
                                          match (uu____79498, uu____79499)
                                          with
                                          | ((topt,f),(uu____79556,uu____79557,
                                                       (uu____79558,f_branch,t_branch)))
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
                                                    let uu____79614 =
                                                      type_leq g t1 t_branch
                                                       in
                                                    if uu____79614
                                                    then
                                                      FStar_Pervasives_Native.Some
                                                        t_branch
                                                    else
                                                      (let uu____79621 =
                                                         type_leq g t_branch
                                                           t1
                                                          in
                                                       if uu____79621
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
                                 (match uu____79456 with
                                  | (topt,f_match) ->
                                      let mlbranches2 =
                                        FStar_All.pipe_right mlbranches1
                                          (FStar_List.map
                                             (fun uu____79719  ->
                                                match uu____79719 with
                                                | (p,(wopt,uu____79748),
                                                   (b1,uu____79750,t1)) ->
                                                    let b2 =
                                                      match topt with
                                                      | FStar_Pervasives_Native.None
                                                           ->
                                                          FStar_Extraction_ML_Syntax.apply_obj_repr
                                                            b1 t1
                                                      | FStar_Pervasives_Native.Some
                                                          uu____79769 -> b1
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
                                      let uu____79774 =
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             t_match)
                                          (FStar_Extraction_ML_Syntax.MLE_Match
                                             (e1, mlbranches2))
                                         in
                                      (uu____79774, f_match, t_match)))))))

let (ind_discriminator_body :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlmodule1)
  =
  fun env  ->
    fun discName  ->
      fun constrName  ->
        let uu____79801 =
          let uu____79806 =
            FStar_TypeChecker_Env.lookup_lid
              env.FStar_Extraction_ML_UEnv.env_tcenv discName
             in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____79806  in
        match uu____79801 with
        | (uu____79831,fstar_disc_type) ->
            let wildcards =
              let uu____79841 =
                let uu____79842 = FStar_Syntax_Subst.compress fstar_disc_type
                   in
                uu____79842.FStar_Syntax_Syntax.n  in
              match uu____79841 with
              | FStar_Syntax_Syntax.Tm_arrow (binders,uu____79853) ->
                  let uu____79874 =
                    FStar_All.pipe_right binders
                      (FStar_List.filter
                         (fun uu___620_79908  ->
                            match uu___620_79908 with
                            | (uu____79916,FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____79917)) ->
                                true
                            | uu____79922 -> false))
                     in
                  FStar_All.pipe_right uu____79874
                    (FStar_List.map
                       (fun uu____79958  ->
                          let uu____79965 = fresh "_"  in
                          (uu____79965, FStar_Extraction_ML_Syntax.MLTY_Top)))
              | uu____79969 -> failwith "Discriminator must be a function"
               in
            let mlid = fresh "_discr_"  in
            let targ = FStar_Extraction_ML_Syntax.MLTY_Top  in
            let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top  in
            let discrBody =
              let uu____79984 =
                let uu____79985 =
                  let uu____79997 =
                    let uu____79998 =
                      let uu____79999 =
                        let uu____80014 =
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty targ)
                            (FStar_Extraction_ML_Syntax.MLE_Name ([], mlid))
                           in
                        let uu____80020 =
                          let uu____80031 =
                            let uu____80040 =
                              let uu____80041 =
                                let uu____80048 =
                                  FStar_Extraction_ML_Syntax.mlpath_of_lident
                                    constrName
                                   in
                                (uu____80048,
                                  [FStar_Extraction_ML_Syntax.MLP_Wild])
                                 in
                              FStar_Extraction_ML_Syntax.MLP_CTor uu____80041
                               in
                            let uu____80051 =
                              FStar_All.pipe_left
                                (FStar_Extraction_ML_Syntax.with_ty
                                   FStar_Extraction_ML_Syntax.ml_bool_ty)
                                (FStar_Extraction_ML_Syntax.MLE_Const
                                   (FStar_Extraction_ML_Syntax.MLC_Bool true))
                               in
                            (uu____80040, FStar_Pervasives_Native.None,
                              uu____80051)
                             in
                          let uu____80055 =
                            let uu____80066 =
                              let uu____80075 =
                                FStar_All.pipe_left
                                  (FStar_Extraction_ML_Syntax.with_ty
                                     FStar_Extraction_ML_Syntax.ml_bool_ty)
                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                     (FStar_Extraction_ML_Syntax.MLC_Bool
                                        false))
                                 in
                              (FStar_Extraction_ML_Syntax.MLP_Wild,
                                FStar_Pervasives_Native.None, uu____80075)
                               in
                            [uu____80066]  in
                          uu____80031 :: uu____80055  in
                        (uu____80014, uu____80020)  in
                      FStar_Extraction_ML_Syntax.MLE_Match uu____79999  in
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.ml_bool_ty) uu____79998
                     in
                  ((FStar_List.append wildcards [(mlid, targ)]), uu____79997)
                   in
                FStar_Extraction_ML_Syntax.MLE_Fun uu____79985  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty disc_ty) uu____79984
               in
            let uu____80136 =
              let uu____80137 =
                let uu____80140 =
                  let uu____80141 =
                    FStar_Extraction_ML_UEnv.convIdent
                      discName.FStar_Ident.ident
                     in
                  {
                    FStar_Extraction_ML_Syntax.mllb_name = uu____80141;
                    FStar_Extraction_ML_Syntax.mllb_tysc =
                      FStar_Pervasives_Native.None;
                    FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                    FStar_Extraction_ML_Syntax.mllb_def = discrBody;
                    FStar_Extraction_ML_Syntax.mllb_meta = [];
                    FStar_Extraction_ML_Syntax.print_typ = false
                  }  in
                [uu____80140]  in
              (FStar_Extraction_ML_Syntax.NonRec, uu____80137)  in
            FStar_Extraction_ML_Syntax.MLM_Let uu____80136
  