open Prims
exception Un_extractable 
let uu___is_Un_extractable : Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Un_extractable  -> true | uu____4 -> false
  
let type_leq :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlty -> Prims.bool
  =
  fun g  ->
    fun t1  ->
      fun t2  ->
        FStar_Extraction_ML_Util.type_leq
          (FStar_Extraction_ML_Util.udelta_unfold g) t1 t2
  
let type_leq_c :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.mlexpr Prims.option ->
      FStar_Extraction_ML_Syntax.mlty ->
        FStar_Extraction_ML_Syntax.mlty ->
          (Prims.bool * FStar_Extraction_ML_Syntax.mlexpr Prims.option)
  =
  fun g  ->
    fun t1  ->
      fun t2  ->
        FStar_Extraction_ML_Util.type_leq_c
          (FStar_Extraction_ML_Util.udelta_unfold g) t1 t2
  
let erasableType :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.mlty -> Prims.bool
  =
  fun g  ->
    fun t  ->
      FStar_Extraction_ML_Util.erasableType
        (FStar_Extraction_ML_Util.udelta_unfold g) t
  
let eraseTypeDeep :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty
  =
  fun g  ->
    fun t  ->
      FStar_Extraction_ML_Util.eraseTypeDeep
        (FStar_Extraction_ML_Util.udelta_unfold g) t
  
let record_fields fs vs =
  FStar_List.map2 (fun f  -> fun e  -> ((f.FStar_Ident.idText), e)) fs vs 
let fail r msg =
  (let _0_338 =
     let _0_337 = FStar_Range.string_of_range r  in
     FStar_Util.format2 "%s: %s\n" _0_337 msg  in
   FStar_All.pipe_left FStar_Util.print_string _0_338);
  failwith msg 
let err_uninst env t uu____105 app =
  match uu____105 with
  | (vars,ty) ->
      let _0_344 =
        let _0_343 = FStar_Syntax_Print.term_to_string t  in
        let _0_342 =
          let _0_339 = FStar_All.pipe_right vars (FStar_List.map Prims.fst)
             in
          FStar_All.pipe_right _0_339 (FStar_String.concat ", ")  in
        let _0_341 =
          FStar_Extraction_ML_Code.string_of_mlty
            env.FStar_Extraction_ML_UEnv.currentModule ty
           in
        let _0_340 = FStar_Syntax_Print.term_to_string app  in
        FStar_Util.format4
          "Variable %s has a polymorphic type (forall %s. %s); expected it to be fully instantiated, but got %s"
          _0_343 _0_342 _0_341 _0_340
         in
      fail t.FStar_Syntax_Syntax.pos _0_344
  
let err_ill_typed_application env t args ty =
  let _0_349 =
    let _0_348 = FStar_Syntax_Print.term_to_string t  in
    let _0_347 =
      let _0_345 =
        FStar_All.pipe_right args
          (FStar_List.map
             (fun uu____164  ->
                match uu____164 with
                | (x,uu____168) -> FStar_Syntax_Print.term_to_string x))
         in
      FStar_All.pipe_right _0_345 (FStar_String.concat " ")  in
    let _0_346 =
      FStar_Extraction_ML_Code.string_of_mlty
        env.FStar_Extraction_ML_UEnv.currentModule ty
       in
    FStar_Util.format3
      "Ill-typed application: application is %s \n remaining args are %s\nml type of head is %s\n"
      _0_348 _0_347 _0_346
     in
  fail t.FStar_Syntax_Syntax.pos _0_349 
let err_value_restriction t =
  let _0_352 =
    let _0_351 = FStar_Syntax_Print.tag_of_term t  in
    let _0_350 = FStar_Syntax_Print.term_to_string t  in
    FStar_Util.format2
      "Refusing to generalize because of the value restriction: (%s) %s"
      _0_351 _0_350
     in
  fail t.FStar_Syntax_Syntax.pos _0_352 
let err_unexpected_eff t f0 f1 =
  let _0_354 =
    let _0_353 = FStar_Syntax_Print.term_to_string t  in
    FStar_Util.format3 "for expression %s, Expected effect %s; got effect %s"
      _0_353 (FStar_Extraction_ML_Util.eff_to_string f0)
      (FStar_Extraction_ML_Util.eff_to_string f1)
     in
  fail t.FStar_Syntax_Syntax.pos _0_354 
let effect_as_etag :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Ident.lident -> FStar_Extraction_ML_Syntax.e_tag
  =
  let cache = FStar_Util.smap_create (Prims.parse_int "20")  in
  let rec delta_norm_eff g l =
    let uu____214 = FStar_Util.smap_try_find cache l.FStar_Ident.str  in
    match uu____214 with
    | Some l -> l
    | None  ->
        let res =
          let uu____238 =
            FStar_TypeChecker_Env.lookup_effect_abbrev
              g.FStar_Extraction_ML_UEnv.tcenv [FStar_Syntax_Syntax.U_zero] l
             in
          match uu____218 with
          | None  -> l
          | Some (uu____224,c) ->
              delta_norm_eff g (FStar_Syntax_Util.comp_effect_name c)
           in
        (FStar_Util.smap_add cache l.FStar_Ident.str res; res)
     in
  fun g  ->
    fun l  ->
      let l = delta_norm_eff g l  in
      match FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid with
      | true  -> FStar_Extraction_ML_Syntax.E_PURE
      | uu____232 ->
          (match FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GHOST_lid
           with
           | true  -> FStar_Extraction_ML_Syntax.E_GHOST
           | uu____233 -> FStar_Extraction_ML_Syntax.E_IMPURE)
  
let rec is_arity :
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let t = FStar_Syntax_Util.unmeta t  in
      let uu____241 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
         in
      match uu____241 with
      | FStar_Syntax_Syntax.Tm_unknown 
        |FStar_Syntax_Syntax.Tm_delayed _
         |FStar_Syntax_Syntax.Tm_ascribed _|FStar_Syntax_Syntax.Tm_meta _ ->
          failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_uvar _
        |FStar_Syntax_Syntax.Tm_constant _
         |FStar_Syntax_Syntax.Tm_name _|FStar_Syntax_Syntax.Tm_bvar _ ->
          false
      | FStar_Syntax_Syntax.Tm_type uu____272 -> true
      | FStar_Syntax_Syntax.Tm_arrow (uu____273,c) ->
          is_arity env (FStar_Syntax_Util.comp_result c)
      | FStar_Syntax_Syntax.Tm_fvar uu____285 ->
          let t2 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Normalize.AllowUnboundUniverses;
              FStar_TypeChecker_Normalize.EraseUniverses;
              FStar_TypeChecker_Normalize.UnfoldUntil
                FStar_Syntax_Syntax.Delta_constant]
              env.FStar_Extraction_ML_UEnv.tcenv t
             in
          let uu____264 =
            (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n  in
          (match uu____264 with
           | FStar_Syntax_Syntax.Tm_fvar uu____265 -> false
           | uu____266 -> is_arity env t)
      | FStar_Syntax_Syntax.Tm_app uu____267 ->
          let uu____277 = FStar_Syntax_Util.head_and_args t  in
          (match uu____277 with | (head,uu____288) -> is_arity env head)
      | FStar_Syntax_Syntax.Tm_uinst (head,uu____304) -> is_arity env head
      | FStar_Syntax_Syntax.Tm_refine (x,uu____310) ->
          is_arity env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_abs (_,body,_)|FStar_Syntax_Syntax.Tm_let
        (_,body) -> is_arity env body
      | FStar_Syntax_Syntax.Tm_match (uu____365,branches) ->
          (match branches with
           | (uu____367,uu____368,e)::uu____370 -> is_arity env e
           | uu____406 -> false)
  
let rec is_type_aux :
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let t = FStar_Syntax_Subst.compress t  in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed _|FStar_Syntax_Syntax.Tm_unknown  ->
          failwith
            (let _0_355 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: %s" _0_355)
      | FStar_Syntax_Syntax.Tm_constant uu____426 -> false
      | FStar_Syntax_Syntax.Tm_type _
        |FStar_Syntax_Syntax.Tm_refine _|FStar_Syntax_Syntax.Tm_arrow _ ->
          true
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.failwith_lid ->
          false
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____460 =
            FStar_TypeChecker_Env.is_type_constructor
              env.FStar_Extraction_ML_UEnv.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____432 with
           | true  -> true
           | uu____437 ->
               let uu____438 =
                 FStar_TypeChecker_Env.lookup_lid
                   env.FStar_Extraction_ML_UEnv.tcenv
                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  in
               (match uu____438 with | (uu____445,t) -> is_arity env t))
      | FStar_Syntax_Syntax.Tm_uvar (_,t)
        |FStar_Syntax_Syntax.Tm_bvar
         { FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _;
           FStar_Syntax_Syntax.sort = t2;_}|FStar_Syntax_Syntax.Tm_name
         { FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _;
           FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____499,uu____500) ->
          is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____530) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_abs (uu____535,body,uu____537) ->
          is_type_aux env body
      | FStar_Syntax_Syntax.Tm_let (uu____560,body) -> is_type_aux env body
      | FStar_Syntax_Syntax.Tm_match (uu____572,branches) ->
          (match branches with
           | (uu____557,uu____558,e)::uu____560 -> is_type_aux env e
           | uu____596 -> failwith "Empty branches")
      | FStar_Syntax_Syntax.Tm_meta (t,uu____609) -> is_type_aux env t
      | FStar_Syntax_Syntax.Tm_app (head,uu____615) -> is_type_aux env head
  
let is_type :
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let b = is_type_aux env t  in
      FStar_Extraction_ML_UEnv.debug env
        (fun uu____638  ->
           match b with
           | true  ->
               let _0_357 = FStar_Syntax_Print.term_to_string t  in
               let _0_356 = FStar_Syntax_Print.tag_of_term t  in
               FStar_Util.print2 "is_type %s (%s)\n" _0_357 _0_356
           | uu____639 ->
               let _0_359 = FStar_Syntax_Print.term_to_string t  in
               let _0_358 = FStar_Syntax_Print.tag_of_term t  in
               FStar_Util.print2 "not a type %s (%s)\n" _0_359 _0_358);
      b
  
let is_type_binder env x =
  is_arity env (Prims.fst x).FStar_Syntax_Syntax.sort 
let is_constructor : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____659 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n  in
    match uu____659 with
    | FStar_Syntax_Syntax.Tm_fvar
      { FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _;
        FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor );_}
      |FStar_Syntax_Syntax.Tm_fvar
      { FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _;
        FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor
          _);_}
        -> true
    | uu____665 -> false
  
let rec is_fstar_value : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____669 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n  in
    match uu____669 with
    | FStar_Syntax_Syntax.Tm_constant _
      |FStar_Syntax_Syntax.Tm_bvar _
       |FStar_Syntax_Syntax.Tm_fvar _|FStar_Syntax_Syntax.Tm_abs _ -> true
    | FStar_Syntax_Syntax.Tm_app (head,args) ->
        let uu____690 = is_constructor head  in
        (match uu____690 with
         | true  ->
             FStar_All.pipe_right args
               (FStar_List.for_all
                  (fun uu____698  ->
                     match uu____698 with
                     | (te,uu____702) -> is_fstar_value te))
         | uu____703 -> false)
    | FStar_Syntax_Syntax.Tm_meta (t,_)|FStar_Syntax_Syntax.Tm_ascribed
      (t,_,_) -> is_fstar_value t
    | uu____723 -> false
  
let rec is_ml_value : FStar_Extraction_ML_Syntax.mlexpr -> Prims.bool =
  fun e  ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_Const _
      |FStar_Extraction_ML_Syntax.MLE_Var _
       |FStar_Extraction_ML_Syntax.MLE_Name _
        |FStar_Extraction_ML_Syntax.MLE_Fun _ -> true
    | FStar_Extraction_ML_Syntax.MLE_CTor (_,exps)
      |FStar_Extraction_ML_Syntax.MLE_Tuple exps ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Record (uu____794,fields) ->
        FStar_Util.for_all
          (fun uu____748  ->
             match uu____748 with | (uu____751,e) -> is_ml_value e) fields
    | uu____753 -> false
  
let normalize_abs : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t0  ->
    let rec aux bs t copt =
      let t = FStar_Syntax_Subst.compress t  in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_abs (bs',body,copt) ->
          aux (FStar_List.append bs bs') body copt
      | uu____813 ->
          let e' = FStar_Syntax_Util.unascribe t  in
          let uu____815 = FStar_Syntax_Util.is_fun e'  in
          (match uu____815 with
           | true  -> aux bs e' copt
           | uu____816 -> FStar_Syntax_Util.abs bs e' copt)
       in
    aux [] t0 None
  
let unit_binder : FStar_Syntax_Syntax.binder =
  let _0_360 =
    FStar_Syntax_Syntax.new_bv None FStar_TypeChecker_Common.t_unit  in
  FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder _0_360 
let check_pats_for_ite :
  (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option *
    FStar_Syntax_Syntax.term) Prims.list ->
    (Prims.bool * FStar_Syntax_Syntax.term Prims.option *
      FStar_Syntax_Syntax.term Prims.option)
  =
  fun l  ->
    let def = (false, None, None)  in
    match (FStar_List.length l) <> (Prims.parse_int "2") with
    | true  -> def
    | uu____866 ->
        let uu____867 = FStar_List.hd l  in
        (match uu____867 with
         | (p1,w1,e1) ->
             let uu____886 = FStar_List.hd (FStar_List.tl l)  in
             (match uu____886 with
              | (p2,w2,e2) ->
                  (match (w1, w2, (p1.FStar_Syntax_Syntax.v),
                           (p2.FStar_Syntax_Syntax.v))
                   with
                   | (None ,None ,FStar_Syntax_Syntax.Pat_constant
                      (FStar_Const.Const_bool (true
                      )),FStar_Syntax_Syntax.Pat_constant
                      (FStar_Const.Const_bool (false ))) ->
                       (true, (Some e1), (Some e2))
                   | (None ,None ,FStar_Syntax_Syntax.Pat_constant
                      (FStar_Const.Const_bool (false
                      )),FStar_Syntax_Syntax.Pat_constant
                      (FStar_Const.Const_bool (true ))) ->
                       (true, (Some e2), (Some e1))
                   | uu____924 -> def)))
  
let instantiate :
  FStar_Extraction_ML_Syntax.mltyscheme ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty
  = fun s  -> fun args  -> FStar_Extraction_ML_Util.subst s args 
let erasable :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.e_tag ->
      FStar_Extraction_ML_Syntax.mlty -> Prims.bool
  =
  fun g  ->
    fun f  ->
      fun t  ->
        (f = FStar_Extraction_ML_Syntax.E_GHOST) ||
          ((f = FStar_Extraction_ML_Syntax.E_PURE) && (erasableType g t))
  
let erase :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.mlexpr ->
      FStar_Extraction_ML_Syntax.mlty ->
        FStar_Extraction_ML_Syntax.e_tag ->
          (FStar_Extraction_ML_Syntax.mlexpr *
            FStar_Extraction_ML_Syntax.e_tag *
            FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun e  ->
      fun ty  ->
        fun f  ->
          let e =
            let uu____967 = erasable g f ty  in
            match uu____967 with
            | true  ->
                let uu____968 =
                  type_leq g ty FStar_Extraction_ML_Syntax.ml_unit_ty  in
                (match uu____968 with
                 | true  -> FStar_Extraction_ML_Syntax.ml_unit
                 | uu____969 ->
                     FStar_All.pipe_left
                       (FStar_Extraction_ML_Syntax.with_ty ty)
                       (FStar_Extraction_ML_Syntax.MLE_Coerce
                          (FStar_Extraction_ML_Syntax.ml_unit,
                            FStar_Extraction_ML_Syntax.ml_unit_ty, ty)))
            | uu____970 -> e  in
          (e, f, ty)
  
let maybe_coerce :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.mlexpr ->
      FStar_Extraction_ML_Syntax.mlty ->
        FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlexpr
  =
  fun g  ->
    fun e  ->
      fun ty  ->
        fun expect  ->
          let ty = eraseTypeDeep g ty  in
          let uu____984 = (type_leq_c g (Some e) ty) expect  in
          match uu____984 with
          | (true ,Some e') -> e'
          | uu____1055 ->
              (FStar_Extraction_ML_UEnv.debug g
                 (fun uu____1060  ->
                    let uu____1061 =
                      FStar_Extraction_ML_Code.string_of_mlexpr
                        g.FStar_Extraction_ML_UEnv.currentModule e
                       in
                    let _0_362 =
                      FStar_Extraction_ML_Code.string_of_mlty
                        g.FStar_Extraction_ML_UEnv.currentModule ty
                       in
                    let _0_361 =
                      FStar_Extraction_ML_Code.string_of_mlty
                        g.FStar_Extraction_ML_UEnv.currentModule expect
                       in
                    FStar_Util.print3
                      "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n"
                      uu____1061 uu____1062 uu____1063);
               FStar_All.pipe_left
                 (FStar_Extraction_ML_Syntax.with_ty expect)
                 (FStar_Extraction_ML_Syntax.MLE_Coerce (e, ty, expect)))
  
let bv_as_mlty :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlty
  =
  fun g  ->
    fun bv  ->
      let uu____1002 = FStar_Extraction_ML_UEnv.lookup_bv g bv  in
      match uu____1002 with
      | FStar_Util.Inl (uu____1003,t) -> t
      | uu____1010 -> FStar_Extraction_ML_Syntax.MLTY_Top
  
let rec term_as_mlty :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlty
  =
  fun g  ->
    fun t0  ->
      let t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.Iota;
          FStar_TypeChecker_Normalize.Zeta;
          FStar_TypeChecker_Normalize.EraseUniverses;
          FStar_TypeChecker_Normalize.AllowUnboundUniverses]
          g.FStar_Extraction_ML_UEnv.tcenv t0
         in
      let mlt = term_as_mlty' g t  in
      let uu____1044 =
        (fun t  ->
           match t with
           | FStar_Extraction_ML_Syntax.MLTY_Top  -> true
           | FStar_Extraction_ML_Syntax.MLTY_Named uu____1046 ->
               let uu____1050 = FStar_Extraction_ML_Util.udelta_unfold g t
                  in
               (match uu____1050 with
                | None  -> false
                | Some t2 ->
                    (let rec is_top_ty t3 =
                       match t3 with
                       | FStar_Extraction_ML_Syntax.MLTY_Top  -> true
                       | FStar_Extraction_ML_Syntax.MLTY_Named uu____1057 ->
                           let uu____1061 =
                             FStar_Extraction_ML_Util.udelta_unfold g t  in
                           (match uu____1061 with
                            | None  -> false
                            | Some t -> is_top_ty t)
                       | uu____1064 -> false  in
                     is_top_ty) t)
           | uu____1065 -> false) mlt
         in
      match uu____1044 with
      | true  ->
          let t =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Normalize.Beta;
              FStar_TypeChecker_Normalize.Eager_unfolding;
              FStar_TypeChecker_Normalize.UnfoldUntil
                FStar_Syntax_Syntax.Delta_constant;
              FStar_TypeChecker_Normalize.Iota;
              FStar_TypeChecker_Normalize.Zeta;
              FStar_TypeChecker_Normalize.EraseUniverses;
              FStar_TypeChecker_Normalize.AllowUnboundUniverses]
              g.FStar_Extraction_ML_UEnv.tcenv t0
             in
          term_as_mlty' g t
      | uu____1067 -> mlt

and term_as_mlty' :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlty
  =
  fun env  ->
    fun t  ->
      let t = FStar_Syntax_Subst.compress t  in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_bvar _
        |FStar_Syntax_Syntax.Tm_delayed _|FStar_Syntax_Syntax.Tm_unknown  ->
          failwith
            (let _0_364 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format1 "Impossible: Unexpected term %s" _0_364)
      | FStar_Syntax_Syntax.Tm_constant uu____1073 ->
          FStar_Extraction_ML_UEnv.unknownType
      | FStar_Syntax_Syntax.Tm_uvar uu____1145 ->
          FStar_Extraction_ML_UEnv.unknownType
      | FStar_Syntax_Syntax.Tm_meta (t2,_)
        |FStar_Syntax_Syntax.Tm_refine
         ({ FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _;
            FStar_Syntax_Syntax.sort = t2;_},_)
         |FStar_Syntax_Syntax.Tm_uinst (t2,_)|FStar_Syntax_Syntax.Tm_ascribed
          (t2,_,_) -> term_as_mlty' env t2
      | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
      | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv []
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____1132 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____1132 with
           | (bs,c) ->
               let uu____1137 = binders_as_ml_binders env bs  in
               (match uu____1137 with
                | (mlbs,env) ->
                    let t_ret =
                      let eff =
                        FStar_TypeChecker_Env.norm_eff_name
                          env.FStar_Extraction_ML_UEnv.tcenv
                          (FStar_Syntax_Util.comp_effect_name c)
                         in
                      let ed =
                        FStar_TypeChecker_Env.get_effect_decl
                          env.FStar_Extraction_ML_UEnv.tcenv eff
                         in
                      let uu____1154 =
                        FStar_All.pipe_right
                          ed.FStar_Syntax_Syntax.qualifiers
                          (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                         in
                      match uu____1154 with
                      | true  ->
                          let t =
                            FStar_TypeChecker_Util.reify_comp
                              env.FStar_Extraction_ML_UEnv.tcenv
                              (FStar_Syntax_Util.lcomp_of_comp c)
                              FStar_Syntax_Syntax.U_unknown
                             in
                          let res = term_as_mlty' env t  in res
                      | uu____1158 ->
                          term_as_mlty' env (FStar_Syntax_Util.comp_result c)
                       in
                    let erase =
                      effect_as_etag env
                        (FStar_Syntax_Util.comp_effect_name c)
                       in
                    let uu____1160 =
                      FStar_List.fold_right
                        (fun uu____1243  ->
                           fun uu____1244  ->
                             match (uu____1243, uu____1244) with
                             | ((uu____1255,t2),(tag,t')) ->
                                 (FStar_Extraction_ML_Syntax.E_PURE,
                                   (FStar_Extraction_ML_Syntax.MLTY_Fun
                                      (t, tag, t')))) mlbs (erase, t_ret)
                       in
                    (match uu____1160 with | (uu____1187,t) -> t)))
      | FStar_Syntax_Syntax.Tm_app (head,args) ->
          let res =
            let uu____1206 =
              (FStar_Syntax_Util.un_uinst head).FStar_Syntax_Syntax.n  in
            match uu____1206 with
            | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
            | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv args
            | FStar_Syntax_Syntax.Tm_app (head2,args') ->
                let uu____1304 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app
                       (head, (FStar_List.append args' args))) None
                    t.FStar_Syntax_Syntax.pos
                   in
                term_as_mlty' env _0_365
            | uu____1244 -> FStar_Extraction_ML_UEnv.unknownType  in
          res
      | FStar_Syntax_Syntax.Tm_abs (bs,ty,uu____1247) ->
          let uu____1270 = FStar_Syntax_Subst.open_term bs ty  in
          (match uu____1270 with
           | (bs,ty) ->
               let uu____1275 = binders_as_ml_binders env bs  in
               (match uu____1275 with | (bts,env) -> term_as_mlty' env ty))
      | FStar_Syntax_Syntax.Tm_type _
        |FStar_Syntax_Syntax.Tm_let _|FStar_Syntax_Syntax.Tm_match _ ->
          FStar_Extraction_ML_UEnv.unknownType

and arg_as_mlty :
  FStar_Extraction_ML_UEnv.env ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual) ->
      FStar_Extraction_ML_Syntax.mlty
  =
  fun g  ->
    fun uu____1293  ->
      match uu____1293 with
      | (a,uu____1297) ->
          let uu____1298 = is_type g a  in
          (match uu____1298 with
           | true  -> term_as_mlty' g a
           | uu____1299 -> FStar_Extraction_ML_UEnv.erasedContent)

and fv_app_as_mlty :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.args -> FStar_Extraction_ML_Syntax.mlty
  =
  fun g  ->
    fun fv  ->
      fun args  ->
        let uu____1379 =
          FStar_Syntax_Util.arrow_formals
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.ty
           in
        match uu____1303 with
        | (formals,t) ->
            let mlargs = FStar_List.map (arg_as_mlty g) args  in
            let mlargs =
              let n_args = FStar_List.length args  in
              match (FStar_List.length formals) > n_args with
              | true  ->
                  let uu____1347 = FStar_Util.first_N n_args formals  in
                  (match uu____1347 with
                   | (uu____1361,rest) ->
                       let _0_366 =
                         FStar_List.map
                           (fun uu____1377  ->
                              FStar_Extraction_ML_UEnv.erasedContent) rest
                          in
                       FStar_List.append mlargs _0_366)
              | uu____1380 -> mlargs  in
            let nm =
              let uu____1382 =
                FStar_Extraction_ML_UEnv.maybe_mangle_type_projector g fv  in
              match uu____1382 with
              | Some p -> p
              | None  ->
                  FStar_Extraction_ML_Syntax.mlpath_of_lident
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            FStar_Extraction_ML_Syntax.MLTY_Named (mlargs, nm)

and binders_as_ml_binders :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.binders ->
      ((FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)
        Prims.list * FStar_Extraction_ML_UEnv.env)
  =
  fun g  ->
    fun bs  ->
      let uu____1475 =
        FStar_All.pipe_right bs
          (FStar_List.fold_left
             (fun uu____1499  ->
                fun b  ->
                  match uu____1499 with
                  | (ml_bs,env) ->
                      let uu____1451 = is_type_binder g b  in
                      (match uu____1451 with
                       | true  ->
                           let b = Prims.fst b  in
                           let env =
                             FStar_Extraction_ML_UEnv.extend_ty env b
                               (Some FStar_Extraction_ML_Syntax.MLTY_Top)
                              in
                           let ml_b =
                             let _0_367 =
                               FStar_Extraction_ML_UEnv.bv_as_ml_termvar b
                                in
                             (_0_367, FStar_Extraction_ML_Syntax.ml_unit_ty)
                              in
                           ((ml_b :: ml_bs), env)
                       | uu____1477 ->
                           let b = Prims.fst b  in
                           let t =
                             term_as_mlty env b.FStar_Syntax_Syntax.sort  in
                           let env =
                             FStar_Extraction_ML_UEnv.extend_bv env b 
                               ([], t) false false false
                              in
                           let ml_b =
                             let _0_368 =
                               FStar_Extraction_ML_UEnv.bv_as_ml_termvar b
                                in
                             (_0_368, t)  in
                           ((ml_b :: ml_bs), env))) ([], g))
         in
      match uu____1397 with | (ml_bs,env) -> ((FStar_List.rev ml_bs), env)

let mk_MLE_Seq :
  FStar_Extraction_ML_Syntax.mlexpr ->
    FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr'
  =
  fun e1  ->
    fun e2  ->
      match ((e1.FStar_Extraction_ML_Syntax.expr),
              (e2.FStar_Extraction_ML_Syntax.expr))
      with
      | (FStar_Extraction_ML_Syntax.MLE_Seq
         es1,FStar_Extraction_ML_Syntax.MLE_Seq es2) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (FStar_List.append es1 es2)
      | (FStar_Extraction_ML_Syntax.MLE_Seq es1,uu____1639) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (FStar_List.append es1 [e2])
      | (uu____1641,FStar_Extraction_ML_Syntax.MLE_Seq es2) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (e1 :: es2)
      | uu____1549 -> FStar_Extraction_ML_Syntax.MLE_Seq [e1; e2]
  
let mk_MLE_Let :
  Prims.bool ->
    FStar_Extraction_ML_Syntax.mlletbinding ->
      FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr'
  =
  fun top_level  ->
    fun lbs  ->
      fun body  ->
        match lbs with
        | (FStar_Extraction_ML_Syntax.NonRec ,quals,lb::[]) when
            Prims.op_Negation top_level ->
            (match lb.FStar_Extraction_ML_Syntax.mllb_tysc with
             | Some ([],t) when t = FStar_Extraction_ML_Syntax.ml_unit_ty ->
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
                    | uu____1666 when
                        (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
                          =
                          FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr
                  with
                  | true  ->
                      (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
                  | uu____1569 ->
                      (match body.FStar_Extraction_ML_Syntax.expr with
                       | FStar_Extraction_ML_Syntax.MLE_Var x when
                           x = lb.FStar_Extraction_ML_Syntax.mllb_name ->
                           (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
                       | uu____1571 when
                           (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
                             =
                             FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr
                           -> body.FStar_Extraction_ML_Syntax.expr
                       | uu____1572 ->
                           mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def
                             body))
             | uu____1573 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body))
        | uu____1575 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body)
  
let resugar_pat :
  FStar_Syntax_Syntax.fv_qual Prims.option ->
    FStar_Extraction_ML_Syntax.mlpattern ->
      FStar_Extraction_ML_Syntax.mlpattern
  =
  fun q  ->
    fun p  ->
      match p with
      | FStar_Extraction_ML_Syntax.MLP_CTor (d,pats) ->
          (match FStar_Extraction_ML_Util.is_xtuple d with
           | Some n1 -> FStar_Extraction_ML_Syntax.MLP_Tuple pats
           | uu____1684 ->
               (match q with
                | Some (FStar_Syntax_Syntax.Record_ctor (ty,fns)) ->
                    let path =
                      FStar_List.map FStar_Ident.text_of_id ty.FStar_Ident.ns
                       in
                    let fs = record_fields fns pats  in
                    FStar_Extraction_ML_Syntax.MLP_Record (path, fs)
                | uu____1605 -> p))
      | uu____1607 -> p
  
let rec extract_one_pat :
  Prims.bool ->
    Prims.bool ->
      FStar_Extraction_ML_UEnv.env ->
        FStar_Syntax_Syntax.pat ->
          FStar_Extraction_ML_Syntax.mlty Prims.option ->
            (FStar_Extraction_ML_UEnv.env *
              (FStar_Extraction_ML_Syntax.mlpattern *
              FStar_Extraction_ML_Syntax.mlexpr Prims.list) Prims.option *
              Prims.bool)
  =
  fun disjunctive_pat  ->
    fun imp  ->
      fun g  ->
        fun p  ->
          fun expected_topt  ->
            let ok t =
              match expected_topt with
              | None  -> true
              | Some t' ->
                  let ok = type_leq g t t'  in
                  ((match Prims.op_Negation ok with
                    | true  ->
                        FStar_Extraction_ML_UEnv.debug g
                          (fun uu____1646  ->
                             let _0_370 =
                               FStar_Extraction_ML_Code.string_of_mlty
                                 g.FStar_Extraction_ML_UEnv.currentModule t'
                                in
                             let _0_369 =
                               FStar_Extraction_ML_Code.string_of_mlty
                                 g.FStar_Extraction_ML_UEnv.currentModule t
                                in
                             FStar_Util.print2
                               "Expected pattern type %s; got pattern type %s\n"
                               _0_370 _0_369)
                    | uu____1647 -> ());
                   ok)
               in
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_disj uu____1752 ->
                failwith "Impossible: Nested disjunctive pattern"
            | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int
                (c,None )) ->
                let i = FStar_Const.Const_int (c, None)  in
                let x = FStar_Extraction_ML_Syntax.gensym ()  in
                let when_clause =
                  let _0_378 =
                    FStar_Extraction_ML_Syntax.MLE_App
                      (let _0_377 =
                         let _0_376 =
                           FStar_All.pipe_left
                             (FStar_Extraction_ML_Syntax.with_ty
                                FStar_Extraction_ML_Syntax.ml_int_ty)
                             (FStar_Extraction_ML_Syntax.MLE_Var x)
                            in
                         let _0_375 =
                           let _0_374 =
                             let _0_373 =
                               let _0_372 =
                                 FStar_Extraction_ML_Util.mlconst_of_const'
                                   p.FStar_Syntax_Syntax.p i
                                  in
                               FStar_All.pipe_left
                                 (fun _0_371  ->
                                    FStar_Extraction_ML_Syntax.MLE_Const
                                      _0_371) _0_372
                                in
                             FStar_All.pipe_left
                               (FStar_Extraction_ML_Syntax.with_ty
                                  FStar_Extraction_ML_Syntax.ml_int_ty)
                               _0_373
                              in
                           [_0_374]  in
                         _0_376 :: _0_375  in
                       (FStar_Extraction_ML_Util.prims_op_equality, _0_377))
                     in
                  FStar_All.pipe_left
                    (FStar_Extraction_ML_Syntax.with_ty
                       FStar_Extraction_ML_Syntax.ml_bool_ty) _0_378
                   in
                let _0_379 = ok FStar_Extraction_ML_Syntax.ml_int_ty  in
                (g,
                  (Some
                     ((FStar_Extraction_ML_Syntax.MLP_Var x), [when_clause])),
                  uu____1791)
            | FStar_Syntax_Syntax.Pat_constant s ->
                let t =
                  FStar_TypeChecker_TcTerm.tc_constant FStar_Range.dummyRange
                    s
                   in
                let mlty = term_as_mlty g t  in
                let _0_382 =
                  Some
                    (let _0_380 =
                       FStar_Extraction_ML_Syntax.MLP_Const
                         (FStar_Extraction_ML_Util.mlconst_of_const'
                            p.FStar_Syntax_Syntax.p s)
                        in
                     (_0_380, []))
                   in
                let _0_381 = ok mlty  in (g, _0_382, _0_381)
            | FStar_Syntax_Syntax.Pat_var x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort  in
                let g =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp
                   in
                let _0_385 =
                  match imp with
                  | true  -> None
                  | uu____1715 ->
                      Some
                        (let _0_383 =
                           FStar_Extraction_ML_Syntax.MLP_Var
                             (FStar_Extraction_ML_Syntax.bv_as_mlident x)
                            in
                         (_0_383, []))
                   in
                let _0_384 = ok mlty  in (g, _0_385, _0_384)
            | FStar_Syntax_Syntax.Pat_wild x when disjunctive_pat ->
                (g, (Some (FStar_Extraction_ML_Syntax.MLP_Wild, [])), true)
            | FStar_Syntax_Syntax.Pat_wild x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort  in
                let g =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp
                   in
                let _0_388 =
                  match imp with
                  | true  -> None
                  | uu____1744 ->
                      Some
                        (let _0_386 =
                           FStar_Extraction_ML_Syntax.MLP_Var
                             (FStar_Extraction_ML_Syntax.bv_as_mlident x)
                            in
                         (_0_386, []))
                   in
                let _0_387 = ok mlty  in (g, _0_388, _0_387)
            | FStar_Syntax_Syntax.Pat_dot_term uu____1749 -> (g, None, true)
            | FStar_Syntax_Syntax.Pat_cons (f,pats) ->
                let uu____1773 =
                  let uu____1776 = FStar_Extraction_ML_UEnv.lookup_fv g f  in
                  match uu____1776 with
                  | FStar_Util.Inr
                      ({
                         FStar_Extraction_ML_Syntax.expr =
                           FStar_Extraction_ML_Syntax.MLE_Name n;
                         FStar_Extraction_ML_Syntax.mlty = uu____1780;
                         FStar_Extraction_ML_Syntax.loc = uu____1781;_},ttys,uu____1783)
                      -> (n, ttys)
                  | uu____1789 -> failwith "Expected a constructor"  in
                (match uu____1773 with
                 | (d,tys) ->
                     let nTyVars = FStar_List.length (Prims.fst tys)  in
                     let uu____1803 = FStar_Util.first_N nTyVars pats  in
                     (match uu____1803 with
                      | (tysVarPats,restPats) ->
                          let f_ty_opt =
                            try
                              let mlty_args =
                                FStar_All.pipe_right tysVarPats
                                  (FStar_List.map
                                     (fun uu____1994  ->
                                        match uu____1994 with
                                        | (p1,uu____2000) ->
                                            (match p1.FStar_Syntax_Syntax.v
                                             with
                                             | FStar_Syntax_Syntax.Pat_dot_term
                                                 (uu____2005,t) ->
                                                 term_as_mlty g t
                                             | uu____2011 ->
                                                 (FStar_Extraction_ML_UEnv.debug
                                                    g
                                                    (fun uu____2013  ->
                                                       let uu____2014 =
                                                         FStar_Syntax_Print.pat_to_string
                                                           p
                                                          in
                                                       FStar_Util.print1
                                                         "Pattern %s is not extractable"
                                                         _0_389);
                                                  Prims.raise Un_extractable))))
                                 in
                              let f_ty =
                                FStar_Extraction_ML_Util.subst tys mlty_args
                                 in
                              Some
                                (FStar_Extraction_ML_Util.uncurry_mlty_fun
                                   f_ty)
                            with | Un_extractable  -> None  in
                          let uu____1909 =
                            FStar_Util.fold_map
                              (fun g1  ->
                                 fun uu____2046  ->
                                   match uu____2046 with
                                   | (p1,imp1) ->
                                       let uu____2057 =
                                         extract_one_pat disjunctive_pat true
                                           g p None
                                          in
                                       (match uu____1935 with
                                        | (g,p,uu____1951) -> (g, p))) g
                              tysVarPats
                             in
                          (match uu____1909 with
                           | (g,tyMLPats) ->
                               let uu____1983 =
                                 FStar_Util.fold_map
                                   (fun uu____2131  ->
                                      fun uu____2132  ->
                                        match (uu____2131, uu____2132) with
                                        | ((g2,f_ty_opt1),(p1,imp1)) ->
                                            let uu____2181 =
                                              match f_ty_opt1 with
                                              | Some (hd1::rest,res) ->
                                                  ((Some (rest, res)),
                                                    (Some hd))
                                              | uu____2091 -> (None, None)
                                               in
                                            (match uu____2059 with
                                             | (f_ty_opt,expected_ty) ->
                                                 let uu____2128 =
                                                   extract_one_pat
                                                     disjunctive_pat false g
                                                     p expected_ty
                                                    in
                                                 (match uu____2128 with
                                                  | (g,p,uu____2150) ->
                                                      ((g, f_ty_opt), p))))
                                   (g, f_ty_opt) restPats
                                  in
                               (match uu____1983 with
                                | ((g,f_ty_opt),restMLPats) ->
                                    let uu____2211 =
                                      let _0_390 =
                                        FStar_All.pipe_right
                                          (FStar_List.append tyMLPats
                                             restMLPats)
                                          (FStar_List.collect
                                             (fun uu___136_2364  ->
                                                match uu___136_2364 with
                                                | Some x -> [x]
                                                | uu____2268 -> []))
                                         in
                                      FStar_All.pipe_right _0_390
                                        FStar_List.split
                                       in
                                    (match uu____2211 with
                                     | (mlPats,when_clauses) ->
                                         let pat_ty_compat =
                                           match f_ty_opt1 with
                                           | Some ([],t) -> ok t
                                           | uu____2298 -> false  in
                                         let _0_393 =
                                           Some
                                             (let _0_392 =
                                                resugar_pat
                                                  f.FStar_Syntax_Syntax.fv_qual
                                                  (FStar_Extraction_ML_Syntax.MLP_CTor
                                                     (d, mlPats))
                                                 in
                                              let _0_391 =
                                                FStar_All.pipe_right
                                                  when_clauses
                                                  FStar_List.flatten
                                                 in
                                              (_0_392, _0_391))
                                            in
                                         (g, _0_393, pat_ty_compat))))))
  
let extract_pat :
  FStar_Extraction_ML_UEnv.env ->
    (FStar_Syntax_Syntax.pat',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.withinfo_t ->
      FStar_Extraction_ML_Syntax.mlty ->
        (FStar_Extraction_ML_UEnv.env * (FStar_Extraction_ML_Syntax.mlpattern
          * FStar_Extraction_ML_Syntax.mlexpr Prims.option) Prims.list *
          Prims.bool)
  =
  fun g  ->
    fun p  ->
      fun expected_t  ->
        let extract_one_pat disj g p expected_t =
          let uu____2363 = extract_one_pat disj false g p expected_t  in
          match uu____2363 with
          | (g,Some (x,v),b) -> (g, (x, v), b)
          | uu____2394 -> failwith "Impossible: Unable to translate pattern"
           in
        let mk_when_clause whens =
          match whens with
          | [] -> None
          | hd::tl ->
              Some
                (FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd tl)
           in
        match p.FStar_Syntax_Syntax.v with
        | FStar_Syntax_Syntax.Pat_disj [] ->
            failwith "Impossible: Empty disjunctive pattern"
        | FStar_Syntax_Syntax.Pat_disj (p::pats) ->
            let uu____2444 = extract_one_pat true g p (Some expected_t)  in
            (match uu____2444 with
             | (g,p,b) ->
                 let uu____2467 =
                   FStar_Util.fold_map
                     (fun b  ->
                        fun p  ->
                          let uu____2479 =
                            extract_one_pat true g p (Some expected_t)  in
                          match uu____2479 with
                          | (uu____2491,p,b') -> ((b && b'), p)) b pats
                    in
                 (match uu____2467 with
                  | (b,ps) ->
                      let ps = p :: ps  in
                      let uu____2528 =
                        FStar_All.pipe_right ps
                          (FStar_List.partition
                             (fun uu___115_2556  ->
                                match uu___115_2556 with
                                | (uu____2560,uu____2561::uu____2562) -> true
                                | uu____2565 -> false))
                         in
                      (match uu____2528 with
                       | (ps_when,rest) ->
                           let ps2 =
                             FStar_All.pipe_right ps_when
                               (FStar_List.map
                                  (fun uu____2754  ->
                                     match uu____2754 with
                                     | (x,whens) ->
                                         let _0_394 = mk_when_clause whens
                                            in
                                         (x, _0_394)))
                              in
                           let res =
                             match rest with
                             | [] -> (g1, ps2, b1)
                             | rest1 ->
                                 let uu____2795 =
                                   let uu____2800 =
                                     let uu____2804 =
                                       let uu____2805 =
                                         FStar_List.map Prims.fst rest1 in
                                       FStar_Extraction_ML_Syntax.MLP_Branch
                                         (FStar_List.map Prims.fst rest)
                                        in
                                     (_0_395, None)  in
                                   _0_396 :: ps  in
                                 (g, _0_397, b)
                              in
                           res)))
        | uu____2664 ->
            let uu____2665 = extract_one_pat false g p (Some expected_t)  in
            (match uu____2665 with
             | (g,(p,whens),b) ->
                 let when_clause = mk_when_clause whens  in
                 (g, [(p, when_clause)], b))
  
let maybe_eta_data_and_project_record :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.fv_qual Prims.option ->
      FStar_Extraction_ML_Syntax.mlty ->
        FStar_Extraction_ML_Syntax.mlexpr ->
          FStar_Extraction_ML_Syntax.mlexpr
  =
  fun g  ->
    fun qual  ->
      fun residualType  ->
        fun mlAppExpr  ->
          let rec eta_args more_args t =
            match t with
            | FStar_Extraction_ML_Syntax.MLTY_Fun (t0,uu____2747,t1) ->
                let x = FStar_Extraction_ML_Syntax.gensym ()  in
                let _0_400 =
                  let _0_399 =
                    let _0_398 =
                      FStar_All.pipe_left
                        (FStar_Extraction_ML_Syntax.with_ty t0)
                        (FStar_Extraction_ML_Syntax.MLE_Var x)
                       in
                    ((x, t0), _0_398)  in
                  _0_399 :: more_args  in
                eta_args _0_400 t1
            | FStar_Extraction_ML_Syntax.MLTY_Named (uu____2756,uu____2757)
                -> ((FStar_List.rev more_args), t)
            | uu____2769 -> failwith "Impossible: Head type is not an arrow"
             in
          let as_record qual e =
            match ((e.FStar_Extraction_ML_Syntax.expr), qual) with
            | (FStar_Extraction_ML_Syntax.MLE_CTor (uu____2787,args),Some
               (FStar_Syntax_Syntax.Record_ctor (tyname,fields))) ->
                let path =
                  FStar_List.map FStar_Ident.text_of_id tyname.FStar_Ident.ns
                   in
                let fields = record_fields fields args  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     e.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_Record (path, fields))
            | uu____2806 -> e  in
          let resugar_and_maybe_eta qual e =
            let uu____2819 = eta_args [] residualType  in
            match uu____2819 with
            | (eargs,tres) ->
                (match eargs with
                 | [] ->
                     FStar_Extraction_ML_Util.resugar_exp (as_record qual e)
                 | uu____2847 ->
                     let uu____2853 = FStar_List.unzip eargs  in
                     (match uu____2853 with
                      | (binders,eargs) ->
                          (match e.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_CTor (head1,args)
                               ->
                               let body =
                                 let uu____3045 =
                                   let uu____3046 =
                                     FStar_All.pipe_left
                                       (FStar_Extraction_ML_Syntax.with_ty
                                          tres)
                                       (FStar_Extraction_ML_Syntax.MLE_CTor
                                          (head,
                                            (FStar_List.append args eargs)))
                                      in
                                   FStar_All.pipe_left (as_record qual)
                                     _0_401
                                    in
                                 FStar_All.pipe_left
                                   FStar_Extraction_ML_Util.resugar_exp
                                   _0_402
                                  in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    e.FStar_Extraction_ML_Syntax.mlty)
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    (binders, body))
                           | uu____2881 ->
                               failwith "Impossible: Not a constructor")))
             in
          match ((mlAppExpr.FStar_Extraction_ML_Syntax.expr), qual) with
          | (uu____3053,None ) -> mlAppExpr
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____3056;
                FStar_Extraction_ML_Syntax.loc = uu____3057;_},mle::args),Some
             (FStar_Syntax_Syntax.Record_projector (constrname,f))) ->
              let f1 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append constrname.FStar_Ident.ns [f])
                 in
              let fn = FStar_Extraction_ML_Util.mlpath_of_lid f  in
              let proj = FStar_Extraction_ML_Syntax.MLE_Proj (mle, fn)  in
              let e =
                match args with
                | [] -> proj
                | uu____2905 ->
                    FStar_Extraction_ML_Syntax.MLE_App
                      (let _0_403 =
                         FStar_All.pipe_left
                           (FStar_Extraction_ML_Syntax.with_ty
                              FStar_Extraction_ML_Syntax.MLTY_Top) proj
                          in
                       (_0_403, args))
                 in
              FStar_Extraction_ML_Syntax.with_ty
                mlAppExpr.FStar_Extraction_ML_Syntax.mlty e
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = _;
                FStar_Extraction_ML_Syntax.loc = _;_},mlargs),Some
             (FStar_Syntax_Syntax.Data_ctor ))
            |(FStar_Extraction_ML_Syntax.MLE_App
              ({
                 FStar_Extraction_ML_Syntax.expr =
                   FStar_Extraction_ML_Syntax.MLE_Name mlp;
                 FStar_Extraction_ML_Syntax.mlty = _;
                 FStar_Extraction_ML_Syntax.loc = _;_},mlargs),Some
              (FStar_Syntax_Syntax.Record_ctor _)) ->
              let uu____3096 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) _0_404
          | (FStar_Extraction_ML_Syntax.MLE_Name mlp,Some
             (FStar_Syntax_Syntax.Data_ctor ))
            |(FStar_Extraction_ML_Syntax.MLE_Name mlp,Some
              (FStar_Syntax_Syntax.Record_ctor _)) ->
              let uu____3102 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) _0_405
          | uu____2927 -> mlAppExpr
  
let maybe_downgrade_eff :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.e_tag ->
      FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.e_tag
  =
  fun g  ->
    fun f  ->
      fun t  ->
        let uu____3117 =
          (f = FStar_Extraction_ML_Syntax.E_GHOST) &&
            (type_leq g t FStar_Extraction_ML_Syntax.ml_unit_ty)
           in
        match uu____2940 with
        | true  -> FStar_Extraction_ML_Syntax.E_PURE
        | uu____2941 -> f
  
let rec term_as_mlexpr :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag *
        FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun t  ->
      let uu____2981 = term_as_mlexpr' g t  in
      match uu____2981 with
      | (e,tag,ty) ->
          let tag = maybe_downgrade_eff g tag ty  in
          (FStar_Extraction_ML_UEnv.debug g
             (fun u  ->
                FStar_Util.print_string
                  (let _0_408 = FStar_Syntax_Print.tag_of_term t  in
                   let _0_407 = FStar_Syntax_Print.term_to_string t  in
                   let _0_406 =
                     FStar_Extraction_ML_Code.string_of_mlty
                       g.FStar_Extraction_ML_UEnv.currentModule ty
                      in
                   FStar_Util.format4
                     "term_as_mlexpr (%s) :  %s has ML type %s and effect %s\n"
                     _0_408 _0_407 _0_406
                     (FStar_Extraction_ML_Util.eff_to_string tag)));
           erase g e ty tag)

and check_term_as_mlexpr :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Extraction_ML_Syntax.e_tag ->
        FStar_Extraction_ML_Syntax.mlty ->
          (FStar_Extraction_ML_Syntax.mlexpr *
            FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun t  ->
      fun f  ->
        fun ty  ->
          let uu____3000 = check_term_as_mlexpr' g t f ty  in
          match uu____3000 with
          | (e,t) ->
              let uu____3007 = erase g e t f  in
              (match uu____3007 with | (r,uu____3014,t) -> (r, t))

and check_term_as_mlexpr' :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Extraction_ML_Syntax.e_tag ->
        FStar_Extraction_ML_Syntax.mlty ->
          (FStar_Extraction_ML_Syntax.mlexpr *
            FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun e0  ->
      fun f  ->
        fun ty  ->
          let uu____3022 = term_as_mlexpr g e0  in
          match uu____3022 with
          | (e,tag,t) ->
              let tag = maybe_downgrade_eff g tag t  in
              (match FStar_Extraction_ML_Util.eff_leq tag f with
               | true  -> let _0_409 = maybe_coerce g e t ty  in (_0_409, ty)
               | uu____3034 -> err_unexpected_eff e0 f tag)

and term_as_mlexpr' :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag *
        FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun top  ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u  ->
           FStar_Util.print_string
             (let _0_412 =
                FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos  in
              let _0_411 = FStar_Syntax_Print.tag_of_term top  in
              let _0_410 = FStar_Syntax_Print.term_to_string top  in
              FStar_Util.format3 "%s: term_as_mlexpr' (%s) :  %s \n" _0_412
                _0_411 _0_410));
      (let t = FStar_Syntax_Subst.compress top  in
       match t.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_unknown 
         |FStar_Syntax_Syntax.Tm_delayed _
          |FStar_Syntax_Syntax.Tm_uvar _|FStar_Syntax_Syntax.Tm_bvar _ ->
           failwith
             (let _0_413 = FStar_Syntax_Print.tag_of_term t  in
              FStar_Util.format1 "Impossible: Unexpected term: %s" _0_413)
       | FStar_Syntax_Syntax.Tm_type _
         |FStar_Syntax_Syntax.Tm_refine _|FStar_Syntax_Syntax.Tm_arrow _ ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Mutable_alloc ))
           ->
           let uu____3062 = term_as_mlexpr' g t  in
           (match uu____3062 with
            | ({
                 FStar_Extraction_ML_Syntax.expr =
                   FStar_Extraction_ML_Syntax.MLE_Let
                   ((FStar_Extraction_ML_Syntax.NonRec ,flags,bodies),continuation);
                 FStar_Extraction_ML_Syntax.mlty = mlty;
                 FStar_Extraction_ML_Syntax.loc = loc;_},tag,typ)
                ->
                ({
                   FStar_Extraction_ML_Syntax.expr =
                     (FStar_Extraction_ML_Syntax.MLE_Let
                        ((FStar_Extraction_ML_Syntax.NonRec,
                           (FStar_Extraction_ML_Syntax.Mutable :: flags),
                           bodies), continuation));
                   FStar_Extraction_ML_Syntax.mlty = mlty;
                   FStar_Extraction_ML_Syntax.loc = loc
                 }, tag, typ)
            | uu____3277 -> failwith "impossible")
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,uu____3098)) ->
           let t = FStar_Syntax_Subst.compress t  in
           (match t.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) when
                FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname ->
                let ed =
                  FStar_TypeChecker_Env.get_effect_decl
                    g.FStar_Extraction_ML_UEnv.tcenv m
                   in
                let uu____3122 =
                  let _0_414 =
                    FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                     in
                  FStar_All.pipe_right _0_414 Prims.op_Negation  in
                (match uu____3122 with
                 | true  -> term_as_mlexpr' g t
                 | uu____3127 ->
                     let ml_result_ty_1 =
                       term_as_mlty g lb.FStar_Syntax_Syntax.lbtyp  in
                     let uu____3129 =
                       term_as_mlexpr g lb.FStar_Syntax_Syntax.lbdef  in
                     (match uu____3129 with
                      | (comp_1,uu____3137,uu____3138) ->
                          let uu____3139 =
                            let k =
                              let _0_417 =
                                let _0_416 =
                                  let _0_415 =
                                    FStar_Util.left
                                      lb.FStar_Syntax_Syntax.lbname
                                     in
                                  FStar_All.pipe_right _0_415
                                    FStar_Syntax_Syntax.mk_binder
                                   in
                                [_0_416]  in
                              FStar_Syntax_Util.abs _0_417 body None  in
                            let uu____3148 = term_as_mlexpr g k  in
                            match uu____3148 with
                            | (ml_k,uu____3155,t_k) ->
                                let m_2 =
                                  match t_k with
                                  | FStar_Extraction_ML_Syntax.MLTY_Fun
                                      (uu____3158,uu____3159,m_2) -> m_2
                                  | uu____3161 -> failwith "Impossible"  in
                                (ml_k, m_2)
                             in
                          (match uu____3139 with
                           | (ml_k,ty) ->
                               let bind =
                                 let _0_419 =
                                   FStar_Extraction_ML_Syntax.MLE_Name
                                     (let _0_418 =
                                        FStar_Extraction_ML_UEnv.monad_op_name
                                          ed "bind"
                                         in
                                      FStar_All.pipe_right _0_418 Prims.fst)
                                    in
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty
                                      FStar_Extraction_ML_Syntax.MLTY_Top)
                                   _0_419
                                  in
                               let _0_420 =
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty ty)
                                   (FStar_Extraction_ML_Syntax.MLE_App
                                      (bind, [comp_1; ml_k]))
                                  in
                               (_0_420, FStar_Extraction_ML_Syntax.E_IMPURE,
                                 ty))))
            | uu____3171 -> term_as_mlexpr' g t)
       | FStar_Syntax_Syntax.Tm_meta (t,_)|FStar_Syntax_Syntax.Tm_uinst (t,_)
           -> term_as_mlexpr' g t
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____3385 =
             FStar_TypeChecker_TcTerm.type_of_tot_term
               g.FStar_Extraction_ML_UEnv.tcenv t
              in
           (match uu____3184 with
            | (uu____3191,ty,uu____3193) ->
                let ml_ty = term_as_mlty g ty  in
                let _0_424 =
                  let _0_423 =
                    let _0_422 =
                      FStar_Extraction_ML_Util.mlconst_of_const'
                        t.FStar_Syntax_Syntax.pos c
                       in
                    FStar_All.pipe_left
                      (fun _0_421  ->
                         FStar_Extraction_ML_Syntax.MLE_Const _0_421) _0_422
                     in
                  FStar_Extraction_ML_Syntax.with_ty ml_ty _0_423  in
                (_0_424, FStar_Extraction_ML_Syntax.E_PURE, ml_ty))
       | FStar_Syntax_Syntax.Tm_name _|FStar_Syntax_Syntax.Tm_fvar _ ->
           let uu____3197 = is_type g t  in
           (match uu____3197 with
            | true  ->
                (FStar_Extraction_ML_Syntax.ml_unit,
                  FStar_Extraction_ML_Syntax.E_PURE,
                  FStar_Extraction_ML_Syntax.ml_unit_ty)
            | uu____3201 ->
                let uu____3202 = FStar_Extraction_ML_UEnv.lookup_term g t  in
                (match uu____3202 with
                 | (FStar_Util.Inl uu____3209,uu____3210) ->
                     (FStar_Extraction_ML_Syntax.ml_unit,
                       FStar_Extraction_ML_Syntax.E_PURE,
                       FStar_Extraction_ML_Syntax.ml_unit_ty)
                 | (FStar_Util.Inr (x,mltys,uu____3229),qual) ->
                     (match mltys with
                      | ([],t) when t = FStar_Extraction_ML_Syntax.ml_unit_ty
                          ->
                          (FStar_Extraction_ML_Syntax.ml_unit,
                            FStar_Extraction_ML_Syntax.E_PURE, t)
                      | ([],t) ->
                          let _0_425 =
                            maybe_eta_data_and_project_record g qual t x  in
                          (_0_425, FStar_Extraction_ML_Syntax.E_PURE, t)
                      | uu____3252 -> err_uninst g t mltys t)))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,copt) ->
           let uu____3281 = FStar_Syntax_Subst.open_term bs body  in
           (match uu____3281 with
            | (bs,body) ->
                let uu____3289 = binders_as_ml_binders g bs  in
                (match uu____3289 with
                 | (ml_bs,env) ->
                     let uu____3306 = term_as_mlexpr env body  in
                     (match uu____3306 with
                      | (ml_body,f,t) ->
                          let uu____3316 =
                            FStar_List.fold_right
                              (fun uu____3533  ->
                                 fun uu____3534  ->
                                   match (uu____3533, uu____3534) with
                                   | ((uu____3545,targ),(f1,t2)) ->
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         (FStar_Extraction_ML_Syntax.MLTY_Fun
                                            (targ, f, t)))) ml_bs (f, t)
                             in
                          (match uu____3316 with
                           | (f,tfun) ->
                               let _0_426 =
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty tfun)
                                   (FStar_Extraction_ML_Syntax.MLE_Fun
                                      (ml_bs, ml_body))
                                  in
                               (_0_426, f, tfun)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.tk = uu____3562;
              FStar_Syntax_Syntax.pos = uu____3563;
              FStar_Syntax_Syntax.vars = uu____3564;_},t1::[])
           ->
           let uu____3376 = term_as_mlexpr' g (Prims.fst t)  in
           (match uu____3376 with
            | (ml,e_tag,mlty) ->
                (ml, FStar_Extraction_ML_Syntax.E_PURE, mlty))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____3599);
              FStar_Syntax_Syntax.tk = uu____3600;
              FStar_Syntax_Syntax.pos = uu____3601;
              FStar_Syntax_Syntax.vars = uu____3602;_},t1::[])
           ->
           let uu____3414 = term_as_mlexpr' g (Prims.fst t)  in
           (match uu____3414 with
            | (ml,e_tag,mlty) ->
                (ml, FStar_Extraction_ML_Syntax.E_IMPURE, mlty))
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let is_total uu___139_3661 =
             match uu___139_3661 with
             | FStar_Util.Inl l -> FStar_Syntax_Util.is_total_lcomp l
             | FStar_Util.Inr (l,flags) ->
                 (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid)
                   ||
                   (FStar_All.pipe_right flags
                      (FStar_List.existsb
                         (fun uu___138_3679  ->
                            match uu___138_3679 with
                            | FStar_Syntax_Syntax.TOTAL  -> true
                            | uu____3469 -> false)))
              in
           let uu____3470 =
             let _0_427 =
               (FStar_Syntax_Subst.compress head).FStar_Syntax_Syntax.n  in
             ((head.FStar_Syntax_Syntax.n), _0_427)  in
           (match uu____3470 with
            | (FStar_Syntax_Syntax.Tm_uvar uu____3476,uu____3477) ->
                let t =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.Iota;
                    FStar_TypeChecker_Normalize.Zeta;
                    FStar_TypeChecker_Normalize.EraseUniverses;
                    FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                    g.FStar_Extraction_ML_UEnv.tcenv t
                   in
                term_as_mlexpr' g t
            | (uu____3487,FStar_Syntax_Syntax.Tm_abs (bs,uu____3489,Some lc))
                when is_total lc ->
                let t1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.Iota;
                    FStar_TypeChecker_Normalize.Zeta;
                    FStar_TypeChecker_Normalize.EraseUniverses;
                    FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                    g.FStar_Extraction_ML_UEnv.tcenv t
                   in
                term_as_mlexpr' g t
            | uu____3518 ->
                let rec extract_app is_data uu____3546 uu____3547 restArgs =
                  match (uu____3546, uu____3547) with
                  | ((mlhead,mlargs_f),(f,t)) ->
                      (match (restArgs, t) with
                       | ([],uu____3595) ->
                           let evaluation_order_guaranteed =
                             (((FStar_List.length mlargs_f) =
                                 (Prims.parse_int "1"))
                                ||
                                (FStar_Extraction_ML_Util.codegen_fsharp ()))
                               ||
                               (match head1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_fvar fv ->
                                    (FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Syntax_Const.op_And)
                                      ||
                                      (FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Syntax_Const.op_Or)
                                | uu____3609 -> false)
                              in
                           let uu____3610 =
                             match evaluation_order_guaranteed with
                             | true  ->
                                 let _0_428 =
                                   FStar_All.pipe_right
                                     (FStar_List.rev mlargs_f)
                                     (FStar_List.map Prims.fst)
                                    in
                                 ([], _0_428)
                             | uu____3637 ->
                                 FStar_List.fold_left
                                   (fun uu____3646  ->
                                      fun uu____3647  ->
                                        match (uu____3646, uu____3647) with
                                        | ((lbs,out_args),(arg,f)) ->
                                            (match (f =
                                                      FStar_Extraction_ML_Syntax.E_PURE)
                                                     ||
                                                     (f =
                                                        FStar_Extraction_ML_Syntax.E_GHOST)
                                             with
                                             | true  ->
                                                 (lbs, (arg :: out_args))
                                             | uu____3700 ->
                                                 let x =
                                                   FStar_Extraction_ML_Syntax.gensym
                                                     ()
                                                    in
                                                 let _0_430 =
                                                   let _0_429 =
                                                     FStar_All.pipe_left
                                                       (FStar_Extraction_ML_Syntax.with_ty
                                                          arg.FStar_Extraction_ML_Syntax.mlty)
                                                       (FStar_Extraction_ML_Syntax.MLE_Var
                                                          x)
                                                      in
                                                   _0_429 :: out_args  in
                                                 (((x, arg) :: lbs), _0_430)))
                                   ([], []) mlargs_f
                              in
                           (match uu____3610 with
                            | (lbs,mlargs) ->
                                let app =
                                  let uu____3948 =
                                    FStar_All.pipe_left
                                      (FStar_Extraction_ML_Syntax.with_ty t1)
                                      (FStar_Extraction_ML_Syntax.MLE_App
                                         (mlhead, mlargs))
                                     in
                                  FStar_All.pipe_left
                                    (maybe_eta_data_and_project_record g
                                       is_data t) _0_431
                                   in
                                let l_app =
                                  FStar_List.fold_right
                                    (fun uu____3953  ->
                                       fun out  ->
                                         match uu____3953 with
                                         | (x,arg) ->
                                             FStar_All.pipe_left
                                               (FStar_Extraction_ML_Syntax.with_ty
                                                  out.FStar_Extraction_ML_Syntax.mlty)
                                               (mk_MLE_Let false
                                                  (FStar_Extraction_ML_Syntax.NonRec,
                                                    [],
                                                    [{
                                                       FStar_Extraction_ML_Syntax.mllb_name
                                                         = x;
                                                       FStar_Extraction_ML_Syntax.mllb_tysc
                                                         =
                                                         (Some
                                                            ([],
                                                              (arg.FStar_Extraction_ML_Syntax.mlty)));
                                                       FStar_Extraction_ML_Syntax.mllb_add_unit
                                                         = false;
                                                       FStar_Extraction_ML_Syntax.mllb_def
                                                         = arg;
                                                       FStar_Extraction_ML_Syntax.print_typ
                                                         = true
                                                     }]) out)) lbs app
                                   in
                                (l_app, f, t))
                       | ((arg,uu____3745)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                          (formal_t,f',t)) when is_type g arg ->
                           let uu____3763 =
                             type_leq g formal_t
                               FStar_Extraction_ML_Syntax.ml_unit_ty
                              in
                           (match uu____3763 with
                            | true  ->
                                let _0_433 =
                                  let _0_432 =
                                    FStar_Extraction_ML_Util.join
                                      arg.FStar_Syntax_Syntax.pos f f'
                                     in
                                  (_0_432, t)  in
                                extract_app is_data
                                  (mlhead,
                                    ((FStar_Extraction_ML_Syntax.ml_unit,
                                       FStar_Extraction_ML_Syntax.E_PURE) ::
                                    mlargs_f)) _0_433 rest
                            | uu____3772 ->
                                failwith
                                  (let _0_437 =
                                     FStar_Extraction_ML_Code.string_of_mlexpr
                                       g.FStar_Extraction_ML_UEnv.currentModule
                                       mlhead
                                      in
                                   let _0_436 =
                                     FStar_Syntax_Print.term_to_string arg
                                      in
                                   let _0_435 =
                                     FStar_Syntax_Print.tag_of_term arg  in
                                   let _0_434 =
                                     FStar_Extraction_ML_Code.string_of_mlty
                                       g.FStar_Extraction_ML_UEnv.currentModule
                                       formal_t
                                      in
                                   FStar_Util.format4
                                     "Impossible: ill-typed application:\n\thead=%s, arg=%s, tag=%s\n\texpected type unit, got %s"
                                     _0_437 _0_436 _0_435 _0_434))
                       | ((e0,uu____3777)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                          (tExpected,f',t)) ->
                           let r = e0.FStar_Syntax_Syntax.pos  in
                           let uu____3796 = term_as_mlexpr g e0  in
                           (match uu____3796 with
                            | (e0,f0,tInferred) ->
                                let e0 =
                                  maybe_coerce g e0 tInferred tExpected  in
                                let _0_439 =
                                  let _0_438 =
                                    FStar_Extraction_ML_Util.join_l r
                                      [f; f'; f0]
                                     in
                                  (_0_438, t)  in
                                extract_app is_data
                                  (mlhead, ((e0, f0) :: mlargs_f)) _0_439
                                  rest)
                       | uu____3812 ->
                           let uu____3819 =
                             FStar_Extraction_ML_Util.udelta_unfold g t  in
                           (match uu____3819 with
                            | Some t ->
                                extract_app is_data (mlhead, mlargs_f) 
                                  (f, t) restArgs
                            | None  ->
                                err_ill_typed_application g top restArgs t))
                   in
                let extract_app_maybe_projector is_data mlhead uu____3855
                  args =
                  match uu____3855 with
                  | (f,t) ->
                      (match is_data with
                       | Some (FStar_Syntax_Syntax.Record_projector
                           uu____4108) ->
                           let rec remove_implicits args2 f1 t2 =
                             match (args2, t2) with
                             | ((a0,Some (FStar_Syntax_Syntax.Implicit
                                 uu____4158))::args3,FStar_Extraction_ML_Syntax.MLTY_Fun
                                (uu____4160,f',t3)) ->
                                 let uu____4185 =
                                   FStar_Extraction_ML_Util.join
                                     a0.FStar_Syntax_Syntax.pos f f'
                                    in
                                 remove_implicits args _0_440 t
                             | uu____3951 -> (args, f, t)  in
                           let uu____3966 = remove_implicits args f t  in
                           (match uu____3966 with
                            | (args,f,t) ->
                                extract_app is_data (mlhead, []) (f, t) args)
                       | uu____3999 ->
                           extract_app is_data (mlhead, []) (f, t) args)
                   in
                let uu____4006 = is_type g t  in
                (match uu____4006 with
                 | true  ->
                     (FStar_Extraction_ML_Syntax.ml_unit,
                       FStar_Extraction_ML_Syntax.E_PURE,
                       FStar_Extraction_ML_Syntax.ml_unit_ty)
                 | uu____4010 ->
                     let head = FStar_Syntax_Util.un_uinst head  in
                     (match head.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_name _
                        |FStar_Syntax_Syntax.Tm_fvar _ ->
                          let uu____4017 =
                            let uu____4024 =
                              FStar_Extraction_ML_UEnv.lookup_term g head  in
                            match uu____4024 with
                            | (FStar_Util.Inr u,q) -> (u, q)
                            | uu____4057 -> failwith "FIXME Ty"  in
                          (match uu____4017 with
                           | ((head_ml,(vars,t),inst_ok),qual) ->
                               let has_typ_apps =
                                 match args with
                                 | (a,uu____4086)::uu____4087 -> is_type g a
                                 | uu____4101 -> false  in
                               let uu____4107 =
                                 match vars with
                                 | uu____4124::uu____4125 when
                                     (Prims.op_Negation has_typ_apps) &&
                                       inst_ok
                                     -> (head_ml, t, args)
                                 | uu____4132 ->
                                     let n = FStar_List.length vars  in
                                     (match n <= (FStar_List.length args)
                                      with
                                      | true  ->
                                          let uu____4152 =
                                            FStar_Util.first_N n args  in
                                          (match uu____4152 with
                                           | (prefix,rest) ->
                                               let prefixAsMLTypes =
                                                 FStar_List.map
                                                   (fun uu____4205  ->
                                                      match uu____4205 with
                                                      | (x,uu____4209) ->
                                                          term_as_mlty g x)
                                                   prefix
                                                  in
                                               let t =
                                                 instantiate (vars, t)
                                                   prefixAsMLTypes
                                                  in
                                               let head =
                                                 match head_ml.FStar_Extraction_ML_Syntax.expr
                                                 with
                                                 | FStar_Extraction_ML_Syntax.MLE_Name
                                                   _
                                                   |FStar_Extraction_ML_Syntax.MLE_Var
                                                   _ ->
                                                     let uu___121_4214 =
                                                       head_ml  in
                                                     {
                                                       FStar_Extraction_ML_Syntax.expr
                                                         =
                                                         (uu___121_4214.FStar_Extraction_ML_Syntax.expr);
                                                       FStar_Extraction_ML_Syntax.mlty
                                                         = t;
                                                       FStar_Extraction_ML_Syntax.loc
                                                         =
                                                         (uu___121_4214.FStar_Extraction_ML_Syntax.loc)
                                                     }
                                                 | FStar_Extraction_ML_Syntax.MLE_App
                                                     (head,{
                                                             FStar_Extraction_ML_Syntax.expr
                                                               =
                                                               FStar_Extraction_ML_Syntax.MLE_Const
                                                               (FStar_Extraction_ML_Syntax.MLC_Unit
                                                               );
                                                             FStar_Extraction_ML_Syntax.mlty
                                                               = uu____4216;
                                                             FStar_Extraction_ML_Syntax.loc
                                                               = uu____4217;_}::[])
                                                     ->
                                                     FStar_All.pipe_right
                                                       (FStar_Extraction_ML_Syntax.MLE_App
                                                          ((let uu___122_4220
                                                              = head  in
                                                            {
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                (uu___122_4220.FStar_Extraction_ML_Syntax.expr);
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                =
                                                                (FStar_Extraction_ML_Syntax.MLTY_Fun
                                                                   (FStar_Extraction_ML_Syntax.ml_unit_ty,
                                                                    FStar_Extraction_ML_Syntax.E_PURE,
                                                                    t));
                                                              FStar_Extraction_ML_Syntax.loc
                                                                =
                                                                (uu___122_4220.FStar_Extraction_ML_Syntax.loc)
                                                            }),
                                                            [FStar_Extraction_ML_Syntax.ml_unit]))
                                                       (FStar_Extraction_ML_Syntax.with_ty
                                                          t)
                                                 | uu____4221 ->
                                                     failwith
                                                       "Impossible: Unexpected head term"
                                                  in
                                               (head, t, rest))
                                      | uu____4227 ->
                                          err_uninst g head (vars, t) top)
                                  in
                               (match uu____4107 with
                                | (head_ml,head_t,args) ->
                                    (match args with
                                     | [] ->
                                         let _0_441 =
                                           maybe_eta_data_and_project_record
                                             g qual head_t head_ml
                                            in
                                         (_0_441,
                                           FStar_Extraction_ML_Syntax.E_PURE,
                                           head_t)
                                     | uu____4259 ->
                                         extract_app_maybe_projector qual
                                           head_ml
                                           (FStar_Extraction_ML_Syntax.E_PURE,
                                             head_t) args)))
                      | uu____4265 ->
                          let uu____4266 = term_as_mlexpr g head  in
                          (match uu____4266 with
                           | (head,f,t) ->
                               extract_app_maybe_projector None head 
                                 (f, t) args))))
       | FStar_Syntax_Syntax.Tm_ascribed (e0,tc,f) ->
           let t =
             match tc with
             | FStar_Util.Inl t1 -> term_as_mlty g t1
             | FStar_Util.Inr c ->
                 term_as_mlty g (FStar_Syntax_Util.comp_result c)
              in
           let f =
             match f with
             | None  -> failwith "Ascription node with an empty effect label"
             | Some l -> effect_as_etag g l  in
           let uu____4314 = check_term_as_mlexpr g e0 f t  in
           (match uu____4314 with | (e,t) -> (e, f, t))
       | FStar_Syntax_Syntax.Tm_let ((is_rec,lbs),e') ->
           let top_level = FStar_Syntax_Syntax.is_top_level lbs  in
           let uu____4335 =
             match is_rec with
             | true  -> FStar_Syntax_Subst.open_let_rec lbs e'
             | uu____4342 ->
                 let uu____4343 = FStar_Syntax_Syntax.is_top_level lbs  in
                 (match uu____4343 with
                  | true  -> (lbs, e')
                  | uu____4350 ->
                      let lb = FStar_List.hd lbs  in
                      let x =
                        FStar_Syntax_Syntax.freshen_bv
                          (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
                         in
                      let lb =
                        let uu___123_4354 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___123_4354.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp =
                            (uu___123_4354.FStar_Syntax_Syntax.lbtyp);
                          FStar_Syntax_Syntax.lbeff =
                            (uu___123_4354.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef =
                            (uu___123_4354.FStar_Syntax_Syntax.lbdef)
                        }  in
                      let e' =
                        FStar_Syntax_Subst.subst
                          [FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x)]
                          e'
                         in
                      ([lb], e'))
              in
           (match uu____4335 with
            | (lbs,e') ->
                let lbs =
                  match top_level with
                  | true  ->
                      FStar_All.pipe_right lbs
                        (FStar_List.map
                           (fun lb  ->
                              let tcenv =
                                let _0_442 =
                                  FStar_Ident.lid_of_path
                                    (FStar_List.append
                                       (Prims.fst
                                          g.FStar_Extraction_ML_UEnv.currentModule)
                                       [Prims.snd
                                          g.FStar_Extraction_ML_UEnv.currentModule])
                                    FStar_Range.dummyRange
                                   in
                                FStar_TypeChecker_Env.set_current_module
                                  g.FStar_Extraction_ML_UEnv.tcenv _0_442
                                 in
                              FStar_Extraction_ML_UEnv.debug g
                                (fun uu____4374  ->
                                   FStar_Options.set_option "debug_level"
                                     (FStar_Options.List
                                        [FStar_Options.String "Norm";
                                        FStar_Options.String "Extraction"]));
                              (let lbdef =
                                 let uu____4378 = FStar_Options.ml_ish ()  in
                                 match uu____4378 with
                                 | true  -> lb.FStar_Syntax_Syntax.lbdef
                                 | uu____4381 ->
                                     FStar_TypeChecker_Normalize.normalize
                                       [FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                                       FStar_TypeChecker_Normalize.EraseUniverses;
                                       FStar_TypeChecker_Normalize.Inlining;
                                       FStar_TypeChecker_Normalize.Eager_unfolding;
                                       FStar_TypeChecker_Normalize.Exclude
                                         FStar_TypeChecker_Normalize.Zeta;
                                       FStar_TypeChecker_Normalize.PureSubtermsWithinComputations;
                                       FStar_TypeChecker_Normalize.Primops]
                                       tcenv lb.FStar_Syntax_Syntax.lbdef
                                  in
                               let uu___124_4382 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___124_4382.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___124_4382.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___124_4382.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___124_4382.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = lbdef
                               })))
                  | uu____4383 -> lbs  in
                let maybe_generalize uu____4396 =
                  match uu____4396 with
                  | { FStar_Syntax_Syntax.lbname = lbname_;
                      FStar_Syntax_Syntax.lbunivs = uu____4665;
                      FStar_Syntax_Syntax.lbtyp = t1;
                      FStar_Syntax_Syntax.lbeff = lbeff;
                      FStar_Syntax_Syntax.lbdef = e;_} ->
                      let f_e = effect_as_etag g lbeff  in
                      let t = FStar_Syntax_Subst.compress t  in
                      (match t.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                           let _0_443 = FStar_List.hd bs  in
                           FStar_All.pipe_right _0_443 (is_type_binder g) ->
                           let uu____4454 = FStar_Syntax_Subst.open_comp bs c
                              in
                           (match uu____4454 with
                            | (bs,c) ->
                                let uu____4468 =
                                  let uu____4473 =
                                    FStar_Util.prefix_until
                                      (fun x  ->
                                         Prims.op_Negation
                                           (is_type_binder g x)) bs
                                     in
                                  match uu____4473 with
                                  | None  ->
                                      (bs, (FStar_Syntax_Util.comp_result c))
                                  | Some (bs,b,rest) ->
                                      let _0_444 =
                                        FStar_Syntax_Util.arrow (b :: rest) c
                                         in
                                      (bs, _0_444)
                                   in
                                (match uu____4468 with
                                 | (tbinders,tbody) ->
                                     let n_tbinders =
                                       FStar_List.length tbinders  in
                                     let e =
                                       let _0_445 = normalize_abs e  in
                                       FStar_All.pipe_right _0_445
                                         FStar_Syntax_Util.unmeta
                                        in
                                     (match e.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Tm_abs
                                          (bs,body,uu____4576) ->
                                          let uu____4599 =
                                            FStar_Syntax_Subst.open_term bs
                                              body
                                             in
                                          (match uu____4599 with
                                           | (bs,body) ->
                                               (match n_tbinders <=
                                                        (FStar_List.length bs)
                                                with
                                                | true  ->
                                                    let uu____4629 =
                                                      FStar_Util.first_N
                                                        n_tbinders bs
                                                       in
                                                    (match uu____4629 with
                                                     | (targs,rest_args) ->
                                                         let expected_source_ty
                                                           =
                                                           let s =
                                                             FStar_List.map2
                                                               (fun
                                                                  uu____4672 
                                                                  ->
                                                                 match 
                                                                   (uu____4938,
                                                                    uu____4939)
                                                                 with
                                                                 | ((x,uu____4949),
                                                                    (y,uu____4951))
                                                                    ->
                                                                    let uu____4956
                                                                    =
                                                                    let uu____4961
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    y  in
                                                                    (x,
                                                                    _0_446)))
                                                               tbinders targs
                                                              in
                                                           FStar_Syntax_Subst.subst
                                                             s tbody
                                                            in
                                                         let env =
                                                           FStar_List.fold_left
                                                             (fun env  ->
                                                                fun
                                                                  uu____4694 
                                                                  ->
                                                                  match uu____4694
                                                                  with
                                                                  | (a,uu____4698)
                                                                    ->
                                                                    FStar_Extraction_ML_UEnv.extend_ty
                                                                    env a
                                                                    None) g
                                                             targs
                                                            in
                                                         let expected_t =
                                                           term_as_mlty env
                                                             expected_source_ty
                                                            in
                                                         let polytype =
                                                           let _0_447 =
                                                             FStar_All.pipe_right
                                                               targs
                                                               (FStar_List.map
                                                                  (fun
                                                                    uu____4719
                                                                     ->
                                                                    match uu____4719
                                                                    with
                                                                    | 
                                                                    (x,uu____4725)
                                                                    ->
                                                                    FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                                    x))
                                                              in
                                                           (_0_447,
                                                             expected_t)
                                                            in
                                                         let add_unit =
                                                           match rest_args
                                                           with
                                                           | [] ->
                                                               Prims.op_Negation
                                                                 (is_fstar_value
                                                                    body)
                                                           | uu____4729 ->
                                                               false
                                                            in
                                                         let rest_args =
                                                           match add_unit
                                                           with
                                                           | true  ->
                                                               unit_binder ::
                                                               rest_args
                                                           | uu____4736 ->
                                                               rest_args
                                                            in
                                                         let body =
                                                           match rest_args
                                                           with
                                                           | [] -> body
                                                           | uu____4738 ->
                                                               FStar_Syntax_Util.abs
                                                                 rest_args
                                                                 body None
                                                            in
                                                         (lbname_, f_e,
                                                           (t,
                                                             (targs,
                                                               polytype)),
                                                           add_unit, body))
                                                | uu____4777 ->
                                                    failwith
                                                      "Not enough type binders"))
                                      | FStar_Syntax_Syntax.Tm_uinst _
                                        |FStar_Syntax_Syntax.Tm_fvar _
                                         |FStar_Syntax_Syntax.Tm_name _ ->
                                          let env =
                                            FStar_List.fold_left
                                              (fun env  ->
                                                 fun uu____5071  ->
                                                   match uu____5071 with
                                                   | (a,uu____5075) ->
                                                       FStar_Extraction_ML_UEnv.extend_ty
                                                         env a None) g
                                              tbinders
                                             in
                                          let expected_t =
                                            term_as_mlty env tbody  in
                                          let polytype =
                                            let uu____5083 =
                                              FStar_All.pipe_right tbinders
                                                (FStar_List.map
                                                   (fun uu____5094  ->
                                                      match uu____5094 with
                                                      | (x,uu____5100) ->
                                                          FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                            x))
                                               in
                                            (_0_448, expected_t)  in
                                          let args =
                                            FStar_All.pipe_right tbinders
                                              (FStar_List.map
                                                 (fun uu____5109  ->
                                                    match uu____5109 with
                                                    | (bv,uu____5113) ->
                                                        let uu____5114 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            bv
                                                           in
                                                        FStar_All.pipe_right
                                                          _0_449
                                                          FStar_Syntax_Syntax.as_arg))
                                             in
                                          let e =
                                            (FStar_Syntax_Syntax.mk
                                               (FStar_Syntax_Syntax.Tm_app
                                                  (e, args))) None
                                              e.FStar_Syntax_Syntax.pos
                                             in
                                          (lbname_, f_e,
                                            (t, (tbinders, polytype)), false,
                                            e)
                                      | uu____4870 -> err_value_restriction e)))
                       | uu____4880 ->
                           let expected_t = term_as_mlty g t  in
                           (lbname_, f_e, (t, ([], ([], expected_t))), false,
                             e))
                   in
                let check_lb env uu____4937 =
                  match uu____4937 with
                  | (nm,(lbname,f,(t,(targs,polytype)),add_unit,e)) ->
                      let env =
                        FStar_List.fold_left
                          (fun env  ->
                             fun uu____5008  ->
                               match uu____5008 with
                               | (a,uu____5012) ->
                                   FStar_Extraction_ML_UEnv.extend_ty env a
                                     None) env targs
                         in
                      let expected_t =
                        match add_unit with
                        | true  ->
                            FStar_Extraction_ML_Syntax.MLTY_Fun
                              (FStar_Extraction_ML_Syntax.ml_unit_ty,
                                FStar_Extraction_ML_Syntax.E_PURE,
                                (Prims.snd polytype))
                        | uu____5014 -> Prims.snd polytype  in
                      let uu____5015 =
                        check_term_as_mlexpr env e f expected_t  in
                      (match uu____5015 with
                       | (e,uu____5021) ->
                           let f = maybe_downgrade_eff env f expected_t  in
                           (f,
                             {
                               FStar_Extraction_ML_Syntax.mllb_name = nm;
                               FStar_Extraction_ML_Syntax.mllb_tysc =
                                 (Some polytype);
                               FStar_Extraction_ML_Syntax.mllb_add_unit =
                                 add_unit;
                               FStar_Extraction_ML_Syntax.mllb_def = e1;
                               FStar_Extraction_ML_Syntax.print_typ = true
                             }))
                   in
                let lbs =
                  FStar_All.pipe_right lbs (FStar_List.map maybe_generalize)
                   in
                let uu____5056 =
                  FStar_List.fold_right
                    (fun lb  ->
                       fun uu____5095  ->
                         match uu____5095 with
                         | (env,lbs) ->
                             let uu____5159 = lb  in
                             (match uu____5159 with
                              | (lbname,uu____5184,(t,(uu____5186,polytype)),add_unit,uu____5189)
                                  ->
                                  let uu____5478 =
                                    FStar_Extraction_ML_UEnv.extend_lb env
                                      lbname t polytype add_unit true
                                     in
                                  (match uu____5196 with
                                   | (env,nm) -> (env, ((nm, lb) :: lbs)))))
                    lbs (g, [])
                   in
                (match uu____5056 with
                 | (env_body,lbs) ->
                     let env_def =
                       match is_rec with
                       | true  -> env_body
                       | uu____5300 -> g  in
                     let lbs =
                       FStar_All.pipe_right lbs
                         (FStar_List.map (check_lb env_def))
                        in
                     let e'_rng = e'.FStar_Syntax_Syntax.pos  in
                     let uu____5339 = term_as_mlexpr env_body e'  in
                     (match uu____5339 with
                      | (e',f',t') ->
                          let f =
                            let _0_451 =
                              let _0_450 = FStar_List.map Prims.fst lbs  in
                              f' :: _0_450  in
                            FStar_Extraction_ML_Util.join_l e'_rng _0_451  in
                          let is_rec =
                            match is_rec = true with
                            | true  -> FStar_Extraction_ML_Syntax.Rec
                            | uu____5353 -> FStar_Extraction_ML_Syntax.NonRec
                             in
                          let _0_456 =
                            let _0_455 =
                              let _0_453 =
                                let _0_452 = FStar_List.map Prims.snd lbs  in
                                (is_rec, [], _0_452)  in
                              mk_MLE_Let top_level _0_453 e'  in
                            let _0_454 =
                              FStar_Extraction_ML_Util.mlloc_of_range
                                t.FStar_Syntax_Syntax.pos
                               in
                            FStar_Extraction_ML_Syntax.with_ty_loc t' _0_455
                              _0_454
                             in
                          (_0_456, f, t'))))
       | FStar_Syntax_Syntax.Tm_match (scrutinee,pats) ->
           let uu____5386 = term_as_mlexpr g scrutinee  in
           (match uu____5386 with
            | (e,f_e,t_e) ->
                let uu____5396 = check_pats_for_ite pats  in
                (match uu____5396 with
                 | (b,then_e,else_e) ->
                     let no_lift x t = x  in
                     (match b with
                      | true  ->
                          (match (then_e, else_e) with
                           | (Some then_e,Some else_e) ->
                               let uu____5431 = term_as_mlexpr g then_e  in
                               (match uu____5431 with
                                | (then_mle,f_then,t_then) ->
                                    let uu____5441 = term_as_mlexpr g else_e
                                       in
                                    (match uu____5441 with
                                     | (else_mle,f_else,t_else) ->
                                         let uu____5451 =
                                           let uu____5458 =
                                             type_leq g t_then t_else  in
                                           match uu____5458 with
                                           | true  -> (t_else, no_lift)
                                           | uu____5469 ->
                                               let uu____5470 =
                                                 type_leq g t_else t_then  in
                                               (match uu____5470 with
                                                | true  -> (t_then, no_lift)
                                                | uu____5481 ->
                                                    (FStar_Extraction_ML_Syntax.MLTY_Top,
                                                      FStar_Extraction_ML_Syntax.apply_obj_repr))
                                            in
                                         (match uu____5451 with
                                          | (t_branch,maybe_lift) ->
                                              let _0_461 =
                                                let _0_459 =
                                                  FStar_Extraction_ML_Syntax.MLE_If
                                                    (let _0_458 =
                                                       maybe_lift then_mle
                                                         t_then
                                                        in
                                                     let _0_457 =
                                                       Some
                                                         (maybe_lift else_mle
                                                            t_else)
                                                        in
                                                     (e, _0_458, _0_457))
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_Extraction_ML_Syntax.with_ty
                                                     t_branch) _0_459
                                                 in
                                              let _0_460 =
                                                FStar_Extraction_ML_Util.join
                                                  then_e.FStar_Syntax_Syntax.pos
                                                  f_then f_else
                                                 in
                                              (_0_461, _0_460, t_branch))))
                           | uu____5500 ->
                               failwith
                                 "ITE pats matched but then and else expressions not found?")
                      | uu____5508 ->
                          let uu____5509 =
                            FStar_All.pipe_right pats
                              (FStar_Util.fold_map
                                 (fun compat  ->
                                    fun br  ->
                                      let uu____5559 =
                                        FStar_Syntax_Subst.open_branch br  in
                                      match uu____5559 with
                                      | (pat,when_opt,branch) ->
                                          let uu____5589 =
                                            extract_pat g pat t_e  in
                                          (match uu____5589 with
                                           | (env,p,pat_t_compat) ->
                                               let uu____5620 =
                                                 match when_opt with
                                                 | None  ->
                                                     (None,
                                                       FStar_Extraction_ML_Syntax.E_PURE)
                                                 | Some w ->
                                                     let uu____5635 =
                                                       term_as_mlexpr env w
                                                        in
                                                     (match uu____5635 with
                                                      | (w,f_w,t_w) ->
                                                          let w =
                                                            maybe_coerce env
                                                              w t_w
                                                              FStar_Extraction_ML_Syntax.ml_bool_ty
                                                             in
                                                          ((Some w), f_w))
                                                  in
                                               (match uu____5620 with
                                                | (when_opt,f_when) ->
                                                    let uu____5663 =
                                                      term_as_mlexpr env
                                                        branch
                                                       in
                                                    (match uu____5663 with
                                                     | (mlbranch,f_branch,t_branch)
                                                         ->
                                                         let _0_462 =
                                                           FStar_All.pipe_right
                                                             p
                                                             (FStar_List.map
                                                                (fun
                                                                   uu____5718
                                                                    ->
                                                                   match uu____5718
                                                                   with
                                                                   | 
                                                                   (p,wopt)
                                                                    ->
                                                                    let when_clause
                                                                    =
                                                                    FStar_Extraction_ML_Util.conjoin_opt
                                                                    wopt
                                                                    when_opt
                                                                     in
                                                                    (p,
                                                                    (when_clause,
                                                                    f_when),
                                                                    (mlbranch,
                                                                    f_branch,
                                                                    t_branch))))
                                                            in
                                                         ((compat &&
                                                             pat_t_compat),
                                                           _0_462))))) true)
                             in
                          (match uu____5509 with
                           | (pat_t_compat,mlbranches) ->
                               let mlbranches = FStar_List.flatten mlbranches
                                  in
                               let e =
                                 match pat_t_compat with
                                 | true  -> e
                                 | uu____5792 ->
                                     (FStar_Extraction_ML_UEnv.debug g
                                        (fun uu____5794  ->
                                           let _0_464 =
                                             FStar_Extraction_ML_Code.string_of_mlexpr
                                               g.FStar_Extraction_ML_UEnv.currentModule
                                               e
                                              in
                                           let _0_463 =
                                             FStar_Extraction_ML_Code.string_of_mlty
                                               g.FStar_Extraction_ML_UEnv.currentModule
                                               t_e
                                              in
                                           FStar_Util.print2
                                             "Coercing scrutinee %s from type %s because pattern type is incompatible\n"
                                             _0_464 _0_463);
                                      FStar_All.pipe_left
                                        (FStar_Extraction_ML_Syntax.with_ty
                                           t_e)
                                        (FStar_Extraction_ML_Syntax.MLE_Coerce
                                           (e, t_e,
                                             FStar_Extraction_ML_Syntax.MLTY_Top)))
                                  in
                               (match mlbranches with
                                | [] ->
                                    let uu____5807 =
                                      let _0_466 =
                                        let _0_465 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            FStar_Syntax_Const.failwith_lid
                                            FStar_Syntax_Syntax.Delta_constant
                                            None
                                           in
                                        FStar_Extraction_ML_UEnv.lookup_fv g
                                          _0_465
                                         in
                                      FStar_All.pipe_left FStar_Util.right
                                        _0_466
                                       in
                                    (match uu____5807 with
                                     | (fw,uu____5830,uu____5831) ->
                                         let _0_470 =
                                           let _0_469 =
                                             FStar_Extraction_ML_Syntax.MLE_App
                                               (let _0_468 =
                                                  let _0_467 =
                                                    FStar_All.pipe_left
                                                      (FStar_Extraction_ML_Syntax.with_ty
                                                         FStar_Extraction_ML_Syntax.ml_string_ty)
                                                      (FStar_Extraction_ML_Syntax.MLE_Const
                                                         (FStar_Extraction_ML_Syntax.MLC_String
                                                            "unreachable"))
                                                     in
                                                  [_0_467]  in
                                                (fw, _0_468))
                                              in
                                           FStar_All.pipe_left
                                             (FStar_Extraction_ML_Syntax.with_ty
                                                FStar_Extraction_ML_Syntax.ml_unit_ty)
                                             _0_469
                                            in
                                         (_0_470,
                                           FStar_Extraction_ML_Syntax.E_PURE,
                                           FStar_Extraction_ML_Syntax.ml_unit_ty))
                                | (uu____5833,uu____5834,(uu____5835,f_first,t_first))::rest
                                    ->
                                    let uu____5867 =
                                      FStar_List.fold_left
                                        (fun uu____5883  ->
                                           fun uu____5884  ->
                                             match (uu____5883, uu____5884)
                                             with
                                             | ((topt,f),(uu____5914,uu____5915,
                                                          (uu____5916,f_branch,t_branch)))
                                                 ->
                                                 let f =
                                                   FStar_Extraction_ML_Util.join
                                                     top.FStar_Syntax_Syntax.pos
                                                     f f_branch
                                                    in
                                                 let topt =
                                                   match topt with
                                                   | None  -> None
                                                   | Some t ->
                                                       let uu____5947 =
                                                         type_leq g t
                                                           t_branch
                                                          in
                                                       (match uu____5947 with
                                                        | true  ->
                                                            Some t_branch
                                                        | uu____5949 ->
                                                            let uu____5950 =
                                                              type_leq g
                                                                t_branch t
                                                               in
                                                            (match uu____5950
                                                             with
                                                             | true  ->
                                                                 Some t
                                                             | uu____5952 ->
                                                                 None))
                                                    in
                                                 (topt, f))
                                        ((Some t_first), f_first) rest
                                       in
                                    (match uu____5867 with
                                     | (topt,f_match) ->
                                         let mlbranches =
                                           FStar_All.pipe_right mlbranches
                                             (FStar_List.map
                                                (fun uu____5996  ->
                                                   match uu____5996 with
                                                   | (p,(wopt,uu____6012),
                                                      (b,uu____6014,t)) ->
                                                       let b =
                                                         match topt with
                                                         | None  ->
                                                             FStar_Extraction_ML_Syntax.apply_obj_repr
                                                               b t
                                                         | Some uu____6025 ->
                                                             b
                                                          in
                                                       (p, wopt, b)))
                                            in
                                         let t_match =
                                           match topt with
                                           | None  ->
                                               FStar_Extraction_ML_Syntax.MLTY_Top
                                           | Some t -> t  in
                                         let _0_471 =
                                           FStar_All.pipe_left
                                             (FStar_Extraction_ML_Syntax.with_ty
                                                t_match)
                                             (FStar_Extraction_ML_Syntax.MLE_Match
                                                (e, mlbranches))
                                            in
                                         (_0_471, f_match, t_match))))))))

let fresh : Prims.string -> (Prims.string * Prims.int) =
  let c = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun x  -> FStar_Util.incr c; (let _0_472 = FStar_ST.read c  in (x, _0_472)) 
let ind_discriminator_body :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlmodule1
  =
  fun env  ->
    fun discName  ->
      fun constrName  ->
        let uu____6057 =
          FStar_TypeChecker_Env.lookup_lid env.FStar_Extraction_ML_UEnv.tcenv
            discName
           in
        match uu____6057 with
        | (uu____6060,fstar_disc_type) ->
            let wildcards =
              let uu____6068 =
                (FStar_Syntax_Subst.compress fstar_disc_type).FStar_Syntax_Syntax.n
                 in
              match uu____6068 with
              | FStar_Syntax_Syntax.Tm_arrow (binders,uu____6075) ->
                  let _0_474 =
                    FStar_All.pipe_right binders
                      (FStar_List.filter
                         (fun uu___118_6105  ->
                            match uu___118_6105 with
                            | (uu____6109,Some (FStar_Syntax_Syntax.Implicit
                               uu____6110)) -> true
                            | uu____6112 -> false))
                     in
                  FStar_All.pipe_right _0_474
                    (FStar_List.map
                       (fun uu____6123  ->
                          let _0_473 = fresh "_"  in
                          (_0_473, FStar_Extraction_ML_Syntax.MLTY_Top)))
              | uu____6129 -> failwith "Discriminator must be a function"  in
            let mlid = fresh "_discr_"  in
            let targ = FStar_Extraction_ML_Syntax.MLTY_Top  in
            let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top  in
            let discrBody =
              let _0_488 =
                FStar_Extraction_ML_Syntax.MLE_Fun
                  (let _0_487 =
                     let _0_486 =
                       FStar_Extraction_ML_Syntax.MLE_Match
                         (let _0_485 =
                            let _0_476 =
                              FStar_Extraction_ML_Syntax.MLE_Name
                                (let _0_475 =
                                   FStar_Extraction_ML_Syntax.idsym mlid  in
                                 ([], _0_475))
                               in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty targ)
                              _0_476
                             in
                          let _0_484 =
                            let _0_483 =
                              let _0_479 =
                                FStar_Extraction_ML_Syntax.MLP_CTor
                                  (let _0_477 =
                                     FStar_Extraction_ML_Syntax.mlpath_of_lident
                                       constrName
                                      in
                                   (_0_477,
                                     [FStar_Extraction_ML_Syntax.MLP_Wild]))
                                 in
                              let _0_478 =
                                FStar_All.pipe_left
                                  (FStar_Extraction_ML_Syntax.with_ty
                                     FStar_Extraction_ML_Syntax.ml_bool_ty)
                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                     (FStar_Extraction_ML_Syntax.MLC_Bool
                                        true))
                                 in
                              (_0_479, None, _0_478)  in
                            let _0_482 =
                              let _0_481 =
                                let _0_480 =
                                  FStar_All.pipe_left
                                    (FStar_Extraction_ML_Syntax.with_ty
                                       FStar_Extraction_ML_Syntax.ml_bool_ty)
                                    (FStar_Extraction_ML_Syntax.MLE_Const
                                       (FStar_Extraction_ML_Syntax.MLC_Bool
                                          false))
                                   in
                                (FStar_Extraction_ML_Syntax.MLP_Wild, None,
                                  _0_480)
                                 in
                              [_0_481]  in
                            _0_483 :: _0_482  in
                          (_0_485, _0_484))
                        in
                     FStar_All.pipe_left
                       (FStar_Extraction_ML_Syntax.with_ty
                          FStar_Extraction_ML_Syntax.ml_bool_ty) _0_486
                      in
                   ((FStar_List.append wildcards [(mlid, targ)]), _0_487))
                 in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty disc_ty) _0_488
               in
            FStar_Extraction_ML_Syntax.MLM_Let
              (let _0_491 =
                 let _0_490 =
                   let _0_489 =
                     FStar_Extraction_ML_UEnv.convIdent
                       discName.FStar_Ident.ident
                      in
                   {
                     FStar_Extraction_ML_Syntax.mllb_name = _0_489;
                     FStar_Extraction_ML_Syntax.mllb_tysc = None;
                     FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                     FStar_Extraction_ML_Syntax.mllb_def = discrBody;
                     FStar_Extraction_ML_Syntax.print_typ = false
                   }  in
                 [_0_490]  in
               (FStar_Extraction_ML_Syntax.NonRec, [], _0_491))
  