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
  (let _0_458 =
     let _0_457 = FStar_Range.string_of_range r  in
     FStar_Util.format2 "%s: %s\n" _0_457 msg  in
   FStar_All.pipe_left FStar_Util.print_string _0_458);
  failwith msg 
let err_uninst env t uu____105 app =
  match uu____105 with
  | (vars,ty) ->
      let _0_464 =
        let _0_463 = FStar_Syntax_Print.term_to_string t  in
        let _0_462 =
          let _0_459 = FStar_All.pipe_right vars (FStar_List.map Prims.fst)
             in
          FStar_All.pipe_right _0_459 (FStar_String.concat ", ")  in
        let _0_461 =
          FStar_Extraction_ML_Code.string_of_mlty
            env.FStar_Extraction_ML_UEnv.currentModule ty
           in
        let _0_460 = FStar_Syntax_Print.term_to_string app  in
        FStar_Util.format4
          "Variable %s has a polymorphic type (forall %s. %s); expected it to be fully instantiated, but got %s"
          _0_463 _0_462 _0_461 _0_460
         in
      fail t.FStar_Syntax_Syntax.pos _0_464
  
let err_ill_typed_application env t args ty =
  let _0_469 =
    let _0_468 = FStar_Syntax_Print.term_to_string t  in
    let _0_467 =
      let _0_465 =
        FStar_All.pipe_right args
          (FStar_List.map
             (fun uu____164  ->
                match uu____164 with
                | (x,uu____168) -> FStar_Syntax_Print.term_to_string x))
         in
      FStar_All.pipe_right _0_465 (FStar_String.concat " ")  in
    let _0_466 =
      FStar_Extraction_ML_Code.string_of_mlty
        env.FStar_Extraction_ML_UEnv.currentModule ty
       in
    FStar_Util.format3
      "Ill-typed application: application is %s \n remaining args are %s\nml type of head is %s\n"
      _0_468 _0_467 _0_466
     in
  fail t.FStar_Syntax_Syntax.pos _0_469 
let err_value_restriction t =
  let _0_472 =
    let _0_471 = FStar_Syntax_Print.tag_of_term t  in
    let _0_470 = FStar_Syntax_Print.term_to_string t  in
    FStar_Util.format2
      "Refusing to generalize because of the value restriction: (%s) %s"
      _0_471 _0_470
     in
  fail t.FStar_Syntax_Syntax.pos _0_472 
let err_unexpected_eff t f0 f1 =
  let _0_474 =
    let _0_473 = FStar_Syntax_Print.term_to_string t  in
    FStar_Util.format3 "for expression %s, Expected effect %s; got effect %s"
      _0_473 (FStar_Extraction_ML_Util.eff_to_string f0)
      (FStar_Extraction_ML_Util.eff_to_string f1)
     in
  fail t.FStar_Syntax_Syntax.pos _0_474 
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
          let uu____218 =
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
      if FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid
      then FStar_Extraction_ML_Syntax.E_PURE
      else
        if FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GHOST_lid
        then FStar_Extraction_ML_Syntax.E_GHOST
        else FStar_Extraction_ML_Syntax.E_IMPURE
  
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
      | FStar_Syntax_Syntax.Tm_type uu____249 -> true
      | FStar_Syntax_Syntax.Tm_arrow (uu____250,c) ->
          is_arity env (FStar_Syntax_Util.comp_result c)
      | FStar_Syntax_Syntax.Tm_fvar uu____262 ->
          let t =
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
      | FStar_Syntax_Syntax.Tm_match (uu____339,branches) ->
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
            (let _0_475 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: %s" _0_475)
      | FStar_Syntax_Syntax.Tm_constant uu____426 -> false
      | FStar_Syntax_Syntax.Tm_type _
        |FStar_Syntax_Syntax.Tm_refine _|FStar_Syntax_Syntax.Tm_arrow _ ->
          true
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.failwith_lid ->
          false
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____432 =
            FStar_TypeChecker_Env.is_type_constructor
              env.FStar_Extraction_ML_UEnv.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          if uu____432
          then true
          else
            (let uu____438 =
               FStar_TypeChecker_Env.lookup_lid
                 env.FStar_Extraction_ML_UEnv.tcenv
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             match uu____438 with | (uu____445,t) -> is_arity env t)
      | FStar_Syntax_Syntax.Tm_uvar (_,t)
        |FStar_Syntax_Syntax.Tm_bvar
         { FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _;
           FStar_Syntax_Syntax.sort = t;_}|FStar_Syntax_Syntax.Tm_name
         { FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _;
           FStar_Syntax_Syntax.sort = t;_}
          -> is_arity env t
      | FStar_Syntax_Syntax.Tm_ascribed (t,uu____466,uu____467) ->
          is_type_aux env t
      | FStar_Syntax_Syntax.Tm_uinst (t,uu____487) -> is_type_aux env t
      | FStar_Syntax_Syntax.Tm_abs (uu____492,body,uu____494) ->
          is_type_aux env body
      | FStar_Syntax_Syntax.Tm_let (uu____517,body) -> is_type_aux env body
      | FStar_Syntax_Syntax.Tm_match (uu____529,branches) ->
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
           if b
           then
             let _0_477 = FStar_Syntax_Print.term_to_string t  in
             let _0_476 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.print2 "is_type %s (%s)\n" _0_477 _0_476
           else
             (let _0_479 = FStar_Syntax_Print.term_to_string t  in
              let _0_478 = FStar_Syntax_Print.tag_of_term t  in
              FStar_Util.print2 "not a type %s (%s)\n" _0_479 _0_478));
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
        if uu____690
        then
          FStar_All.pipe_right args
            (FStar_List.for_all
               (fun uu____698  ->
                  match uu____698 with | (te,uu____702) -> is_fstar_value te))
        else false
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
    | FStar_Extraction_ML_Syntax.MLE_Record (uu____736,fields) ->
        FStar_Util.for_all
          (fun uu____748  ->
             match uu____748 with | (uu____751,e) -> is_ml_value e) fields
    | uu____753 -> false
  
let is_reifiable_effect :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun effect_lid  ->
      let quals = FStar_TypeChecker_Env.lookup_effect_quals env effect_lid
         in
      FStar_List.contains FStar_Syntax_Syntax.Reifiable quals
  
let is_reifiable :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.lcomp,FStar_Syntax_Syntax.residual_comp)
      FStar_Util.either -> Prims.bool
  =
  fun env  ->
    fun c  ->
      let effect_lid =
        match c with
        | FStar_Util.Inl lc -> lc.FStar_Syntax_Syntax.eff_name
        | FStar_Util.Inr (eff_name,uu____775) -> eff_name  in
      is_reifiable_effect env effect_lid
  
let is_reifiable_comp :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.bool =
  fun env  ->
    fun c  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Comp ct ->
          is_reifiable_effect env ct.FStar_Syntax_Syntax.effect_name
      | uu____788 -> false
  
let is_reifiable_function :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____795 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
         in
      match uu____795 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____796,c) -> is_reifiable_comp env c
      | uu____808 -> false
  
let reify_body :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let tm = FStar_Syntax_Util.mk_reify t  in
      let tm' =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Reify;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses;
          FStar_TypeChecker_Normalize.AllowUnboundUniverses] env tm
         in
      (let uu____820 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify")
          in
       if uu____820
       then
         let _0_481 = FStar_Syntax_Print.term_to_string tm  in
         let _0_480 = FStar_Syntax_Print.term_to_string tm'  in
         FStar_Util.print2 "Reified body %s \nto %s\n" _0_481 _0_480
       else ());
      tm'
  
let normalize_abs : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t0  ->
    let rec aux bs t copt =
      let t = FStar_Syntax_Subst.compress t  in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_abs (bs',body,copt) ->
          aux (FStar_List.append bs bs') body copt
      | uu____881 ->
          let e' = FStar_Syntax_Util.unascribe t  in
          let uu____883 = FStar_Syntax_Util.is_fun e'  in
          if uu____883
          then aux bs e' copt
          else FStar_Syntax_Util.abs bs e' copt
       in
    aux [] t0 None
  
let unit_binder : FStar_Syntax_Syntax.binder =
  let _0_482 =
    FStar_Syntax_Syntax.new_bv None FStar_TypeChecker_Common.t_unit  in
  FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder _0_482 
let check_pats_for_ite :
  (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option *
    FStar_Syntax_Syntax.term) Prims.list ->
    (Prims.bool * FStar_Syntax_Syntax.term Prims.option *
      FStar_Syntax_Syntax.term Prims.option)
  =
  fun l  ->
    let def = (false, None, None)  in
    if (FStar_List.length l) <> (Prims.parse_int "2")
    then def
    else
      (let uu____935 = FStar_List.hd l  in
       match uu____935 with
       | (p1,w1,e1) ->
           let uu____954 = FStar_List.hd (FStar_List.tl l)  in
           (match uu____954 with
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
                 | uu____992 -> def)))
  
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
            let uu____1035 = erasable g f ty  in
            if uu____1035
            then
              let uu____1036 =
                type_leq g ty FStar_Extraction_ML_Syntax.ml_unit_ty  in
              (if uu____1036
               then FStar_Extraction_ML_Syntax.ml_unit
               else
                 FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty)
                   (FStar_Extraction_ML_Syntax.MLE_Coerce
                      (FStar_Extraction_ML_Syntax.ml_unit,
                        FStar_Extraction_ML_Syntax.ml_unit_ty, ty)))
            else e  in
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
          let uu____1052 = (type_leq_c g (Some e) ty) expect  in
          match uu____1052 with
          | (true ,Some e') -> e'
          | uu____1058 ->
              (FStar_Extraction_ML_UEnv.debug g
                 (fun uu____1063  ->
                    let _0_485 =
                      FStar_Extraction_ML_Code.string_of_mlexpr
                        g.FStar_Extraction_ML_UEnv.currentModule e
                       in
                    let _0_484 =
                      FStar_Extraction_ML_Code.string_of_mlty
                        g.FStar_Extraction_ML_UEnv.currentModule ty
                       in
                    let _0_483 =
                      FStar_Extraction_ML_Code.string_of_mlty
                        g.FStar_Extraction_ML_UEnv.currentModule expect
                       in
                    FStar_Util.print3
                      "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n"
                      _0_485 _0_484 _0_483);
               FStar_All.pipe_left
                 (FStar_Extraction_ML_Syntax.with_ty expect)
                 (FStar_Extraction_ML_Syntax.MLE_Coerce (e, ty, expect)))
  
let bv_as_mlty :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlty
  =
  fun g  ->
    fun bv  ->
      let uu____1070 = FStar_Extraction_ML_UEnv.lookup_bv g bv  in
      match uu____1070 with
      | FStar_Util.Inl (uu____1071,t) -> t
      | uu____1078 -> FStar_Extraction_ML_Syntax.MLTY_Top
  
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
      let uu____1112 =
        (fun t  ->
           match t with
           | FStar_Extraction_ML_Syntax.MLTY_Top  -> true
           | FStar_Extraction_ML_Syntax.MLTY_Named uu____1114 ->
               let uu____1118 = FStar_Extraction_ML_Util.udelta_unfold g t
                  in
               (match uu____1118 with
                | None  -> false
                | Some t ->
                    (let rec is_top_ty t =
                       match t with
                       | FStar_Extraction_ML_Syntax.MLTY_Top  -> true
                       | FStar_Extraction_ML_Syntax.MLTY_Named uu____1125 ->
                           let uu____1129 =
                             FStar_Extraction_ML_Util.udelta_unfold g t  in
                           (match uu____1129 with
                            | None  -> false
                            | Some t -> is_top_ty t)
                       | uu____1132 -> false  in
                     is_top_ty) t)
           | uu____1133 -> false) mlt
         in
      if uu____1112
      then
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
      else mlt

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
            (let _0_486 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format1 "Impossible: Unexpected term %s" _0_486)
      | FStar_Syntax_Syntax.Tm_constant uu____1141 ->
          FStar_Extraction_ML_UEnv.unknownType
      | FStar_Syntax_Syntax.Tm_uvar uu____1142 ->
          FStar_Extraction_ML_UEnv.unknownType
      | FStar_Syntax_Syntax.Tm_meta (t,_)
        |FStar_Syntax_Syntax.Tm_refine
         ({ FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _;
            FStar_Syntax_Syntax.sort = t;_},_)
         |FStar_Syntax_Syntax.Tm_uinst (t,_)|FStar_Syntax_Syntax.Tm_ascribed
          (t,_,_) -> term_as_mlty' env t
      | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
      | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv []
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____1200 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____1200 with
           | (bs,c) ->
               let uu____1205 = binders_as_ml_binders env bs  in
               (match uu____1205 with
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
                      let uu____1222 =
                        FStar_All.pipe_right
                          ed.FStar_Syntax_Syntax.qualifiers
                          (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                         in
                      if uu____1222
                      then
                        let t =
                          FStar_TypeChecker_Util.reify_comp
                            env.FStar_Extraction_ML_UEnv.tcenv
                            (FStar_Syntax_Util.lcomp_of_comp c)
                            FStar_Syntax_Syntax.U_unknown
                           in
                        let res = term_as_mlty' env t  in res
                      else
                        term_as_mlty' env (FStar_Syntax_Util.comp_result c)
                       in
                    let erase =
                      effect_as_etag env
                        (FStar_Syntax_Util.comp_effect_name c)
                       in
                    let uu____1228 =
                      FStar_List.fold_right
                        (fun uu____1235  ->
                           fun uu____1236  ->
                             match (uu____1235, uu____1236) with
                             | ((uu____1247,t),(tag,t')) ->
                                 (FStar_Extraction_ML_Syntax.E_PURE,
                                   (FStar_Extraction_ML_Syntax.MLTY_Fun
                                      (t, tag, t')))) mlbs (erase, t_ret)
                       in
                    (match uu____1228 with | (uu____1255,t) -> t)))
      | FStar_Syntax_Syntax.Tm_app (head,args) ->
          let res =
            let uu____1274 =
              (FStar_Syntax_Util.un_uinst head).FStar_Syntax_Syntax.n  in
            match uu____1274 with
            | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
            | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv args
            | FStar_Syntax_Syntax.Tm_app (head,args') ->
                let _0_487 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app
                       (head, (FStar_List.append args' args))) None
                    t.FStar_Syntax_Syntax.pos
                   in
                term_as_mlty' env _0_487
            | uu____1312 -> FStar_Extraction_ML_UEnv.unknownType  in
          res
      | FStar_Syntax_Syntax.Tm_abs (bs,ty,uu____1315) ->
          let uu____1338 = FStar_Syntax_Subst.open_term bs ty  in
          (match uu____1338 with
           | (bs,ty) ->
               let uu____1343 = binders_as_ml_binders env bs  in
               (match uu____1343 with | (bts,env) -> term_as_mlty' env ty))
      | FStar_Syntax_Syntax.Tm_type _
        |FStar_Syntax_Syntax.Tm_let _|FStar_Syntax_Syntax.Tm_match _ ->
          FStar_Extraction_ML_UEnv.unknownType

and arg_as_mlty :
  FStar_Extraction_ML_UEnv.env ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual) ->
      FStar_Extraction_ML_Syntax.mlty
  =
  fun g  ->
    fun uu____1361  ->
      match uu____1361 with
      | (a,uu____1365) ->
          let uu____1366 = is_type g a  in
          if uu____1366
          then term_as_mlty' g a
          else FStar_Extraction_ML_UEnv.erasedContent

and fv_app_as_mlty :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.args -> FStar_Extraction_ML_Syntax.mlty
  =
  fun g  ->
    fun fv  ->
      fun args  ->
        let uu____1371 =
          FStar_Syntax_Util.arrow_formals
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.ty
           in
        match uu____1371 with
        | (formals,t) ->
            let mlargs = FStar_List.map (arg_as_mlty g) args  in
            let mlargs =
              let n_args = FStar_List.length args  in
              if (FStar_List.length formals) > n_args
              then
                let uu____1415 = FStar_Util.first_N n_args formals  in
                match uu____1415 with
                | (uu____1429,rest) ->
                    let _0_488 =
                      FStar_List.map
                        (fun uu____1445  ->
                           FStar_Extraction_ML_UEnv.erasedContent) rest
                       in
                    FStar_List.append mlargs _0_488
              else mlargs  in
            let nm =
              let uu____1450 =
                FStar_Extraction_ML_UEnv.maybe_mangle_type_projector g fv  in
              match uu____1450 with
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
      let uu____1465 =
        FStar_All.pipe_right bs
          (FStar_List.fold_left
             (fun uu____1489  ->
                fun b  ->
                  match uu____1489 with
                  | (ml_bs,env) ->
                      let uu____1519 = is_type_binder g b  in
                      if uu____1519
                      then
                        let b = Prims.fst b  in
                        let env =
                          FStar_Extraction_ML_UEnv.extend_ty env b
                            (Some FStar_Extraction_ML_Syntax.MLTY_Top)
                           in
                        let ml_b =
                          let _0_489 =
                            FStar_Extraction_ML_UEnv.bv_as_ml_termvar b  in
                          (_0_489, FStar_Extraction_ML_Syntax.ml_unit_ty)  in
                        ((ml_b :: ml_bs), env)
                      else
                        (let b = Prims.fst b  in
                         let t = term_as_mlty env b.FStar_Syntax_Syntax.sort
                            in
                         let env =
                           FStar_Extraction_ML_UEnv.extend_bv env b ([], t)
                             false false false
                            in
                         let ml_b =
                           let _0_490 =
                             FStar_Extraction_ML_UEnv.bv_as_ml_termvar b  in
                           (_0_490, t)  in
                         ((ml_b :: ml_bs), env))) ([], g))
         in
      match uu____1465 with | (ml_bs,env) -> ((FStar_List.rev ml_bs), env)

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
      | (FStar_Extraction_ML_Syntax.MLE_Seq es1,uu____1612) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (FStar_List.append es1 [e2])
      | (uu____1614,FStar_Extraction_ML_Syntax.MLE_Seq es2) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (e1 :: es2)
      | uu____1617 -> FStar_Extraction_ML_Syntax.MLE_Seq [e1; e2]
  
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
                    | uu____1639 when
                        (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
                          =
                          FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr
                        -> body.FStar_Extraction_ML_Syntax.expr
                    | uu____1640 ->
                        mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def
                          body)
             | uu____1641 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body))
        | uu____1643 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body)
  
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
           | Some n -> FStar_Extraction_ML_Syntax.MLP_Tuple pats
           | uu____1657 ->
               (match q with
                | Some (FStar_Syntax_Syntax.Record_ctor (ty,fns)) ->
                    let path =
                      FStar_List.map FStar_Ident.text_of_id ty.FStar_Ident.ns
                       in
                    let fs = record_fields fns pats  in
                    FStar_Extraction_ML_Syntax.MLP_Record (path, fs)
                | uu____1673 -> p))
      | uu____1675 -> p
  
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
                  (if Prims.op_Negation ok
                   then
                     FStar_Extraction_ML_UEnv.debug g
                       (fun uu____1714  ->
                          let _0_492 =
                            FStar_Extraction_ML_Code.string_of_mlty
                              g.FStar_Extraction_ML_UEnv.currentModule t'
                             in
                          let _0_491 =
                            FStar_Extraction_ML_Code.string_of_mlty
                              g.FStar_Extraction_ML_UEnv.currentModule t
                             in
                          FStar_Util.print2
                            "Expected pattern type %s; got pattern type %s\n"
                            _0_492 _0_491)
                   else ();
                   ok)
               in
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_disj uu____1723 ->
                failwith "Impossible: Nested disjunctive pattern"
            | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int
                (c,None )) ->
                let i = FStar_Const.Const_int (c, None)  in
                let x = FStar_Extraction_ML_Syntax.gensym ()  in
                let when_clause =
                  let _0_500 =
                    FStar_Extraction_ML_Syntax.MLE_App
                      (let _0_499 =
                         let _0_498 =
                           FStar_All.pipe_left
                             (FStar_Extraction_ML_Syntax.with_ty
                                FStar_Extraction_ML_Syntax.ml_int_ty)
                             (FStar_Extraction_ML_Syntax.MLE_Var x)
                            in
                         let _0_497 =
                           let _0_496 =
                             let _0_495 =
                               let _0_494 =
                                 FStar_Extraction_ML_Util.mlconst_of_const'
                                   p.FStar_Syntax_Syntax.p i
                                  in
                               FStar_All.pipe_left
                                 (fun _0_493  ->
                                    FStar_Extraction_ML_Syntax.MLE_Const
                                      _0_493) _0_494
                                in
                             FStar_All.pipe_left
                               (FStar_Extraction_ML_Syntax.with_ty
                                  FStar_Extraction_ML_Syntax.ml_int_ty)
                               _0_495
                              in
                           [_0_496]  in
                         _0_498 :: _0_497  in
                       (FStar_Extraction_ML_Util.prims_op_equality, _0_499))
                     in
                  FStar_All.pipe_left
                    (FStar_Extraction_ML_Syntax.with_ty
                       FStar_Extraction_ML_Syntax.ml_bool_ty) _0_500
                   in
                let _0_501 = ok FStar_Extraction_ML_Syntax.ml_int_ty  in
                (g,
                  (Some
                     ((FStar_Extraction_ML_Syntax.MLP_Var x), [when_clause])),
                  _0_501)
            | FStar_Syntax_Syntax.Pat_constant s ->
                let t =
                  FStar_TypeChecker_TcTerm.tc_constant FStar_Range.dummyRange
                    s
                   in
                let mlty = term_as_mlty g t  in
                let _0_504 =
                  Some
                    (let _0_502 =
                       FStar_Extraction_ML_Syntax.MLP_Const
                         (FStar_Extraction_ML_Util.mlconst_of_const'
                            p.FStar_Syntax_Syntax.p s)
                        in
                     (_0_502, []))
                   in
                let _0_503 = ok mlty  in (g, _0_504, _0_503)
            | FStar_Syntax_Syntax.Pat_var x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort  in
                let g =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp
                   in
                let _0_507 =
                  if imp
                  then None
                  else
                    Some
                      ((let _0_505 =
                          FStar_Extraction_ML_Syntax.MLP_Var
                            (FStar_Extraction_ML_Syntax.bv_as_mlident x)
                           in
                        (_0_505, [])))
                   in
                let _0_506 = ok mlty  in (g, _0_507, _0_506)
            | FStar_Syntax_Syntax.Pat_wild x when disjunctive_pat ->
                (g, (Some (FStar_Extraction_ML_Syntax.MLP_Wild, [])), true)
            | FStar_Syntax_Syntax.Pat_wild x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort  in
                let g =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp
                   in
                let _0_510 =
                  if imp
                  then None
                  else
                    Some
                      ((let _0_508 =
                          FStar_Extraction_ML_Syntax.MLP_Var
                            (FStar_Extraction_ML_Syntax.bv_as_mlident x)
                           in
                        (_0_508, [])))
                   in
                let _0_509 = ok mlty  in (g, _0_510, _0_509)
            | FStar_Syntax_Syntax.Pat_dot_term uu____1817 -> (g, None, true)
            | FStar_Syntax_Syntax.Pat_cons (f,pats) ->
                let uu____1841 =
                  let uu____1844 = FStar_Extraction_ML_UEnv.lookup_fv g f  in
                  match uu____1844 with
                  | FStar_Util.Inr
                      ({
                         FStar_Extraction_ML_Syntax.expr =
                           FStar_Extraction_ML_Syntax.MLE_Name n;
                         FStar_Extraction_ML_Syntax.mlty = uu____1848;
                         FStar_Extraction_ML_Syntax.loc = uu____1849;_},ttys,uu____1851)
                      -> (n, ttys)
                  | uu____1857 -> failwith "Expected a constructor"  in
                (match uu____1841 with
                 | (d,tys) ->
                     let nTyVars = FStar_List.length (Prims.fst tys)  in
                     let uu____1871 = FStar_Util.first_N nTyVars pats  in
                     (match uu____1871 with
                      | (tysVarPats,restPats) ->
                          let f_ty_opt =
                            try
                              let mlty_args =
                                FStar_All.pipe_right tysVarPats
                                  (FStar_List.map
                                     (fun uu____1945  ->
                                        match uu____1945 with
                                        | (p,uu____1951) ->
                                            (match p.FStar_Syntax_Syntax.v
                                             with
                                             | FStar_Syntax_Syntax.Pat_dot_term
                                                 (uu____1956,t) ->
                                                 term_as_mlty g t
                                             | uu____1962 ->
                                                 (FStar_Extraction_ML_UEnv.debug
                                                    g
                                                    (fun uu____1964  ->
                                                       let _0_511 =
                                                         FStar_Syntax_Print.pat_to_string
                                                           p
                                                          in
                                                       FStar_Util.print1
                                                         "Pattern %s is not extractable"
                                                         _0_511);
                                                  Prims.raise Un_extractable))))
                                 in
                              let f_ty =
                                FStar_Extraction_ML_Util.subst tys mlty_args
                                 in
                              Some
                                (FStar_Extraction_ML_Util.uncurry_mlty_fun
                                   f_ty)
                            with | Un_extractable  -> None  in
                          let uu____1977 =
                            FStar_Util.fold_map
                              (fun g  ->
                                 fun uu____1992  ->
                                   match uu____1992 with
                                   | (p,imp) ->
                                       let uu____2003 =
                                         extract_one_pat disjunctive_pat true
                                           g p None
                                          in
                                       (match uu____2003 with
                                        | (g,p,uu____2019) -> (g, p))) g
                              tysVarPats
                             in
                          (match uu____1977 with
                           | (g,tyMLPats) ->
                               let uu____2051 =
                                 FStar_Util.fold_map
                                   (fun uu____2077  ->
                                      fun uu____2078  ->
                                        match (uu____2077, uu____2078) with
                                        | ((g,f_ty_opt),(p,imp)) ->
                                            let uu____2127 =
                                              match f_ty_opt with
                                              | Some (hd::rest,res) ->
                                                  ((Some (rest, res)),
                                                    (Some hd))
                                              | uu____2159 -> (None, None)
                                               in
                                            (match uu____2127 with
                                             | (f_ty_opt,expected_ty) ->
                                                 let uu____2196 =
                                                   extract_one_pat
                                                     disjunctive_pat false g
                                                     p expected_ty
                                                    in
                                                 (match uu____2196 with
                                                  | (g,p,uu____2218) ->
                                                      ((g, f_ty_opt), p))))
                                   (g, f_ty_opt) restPats
                                  in
                               (match uu____2051 with
                                | ((g,f_ty_opt),restMLPats) ->
                                    let uu____2279 =
                                      let _0_512 =
                                        FStar_All.pipe_right
                                          (FStar_List.append tyMLPats
                                             restMLPats)
                                          (FStar_List.collect
                                             (fun uu___133_2314  ->
                                                match uu___133_2314 with
                                                | Some x -> [x]
                                                | uu____2336 -> []))
                                         in
                                      FStar_All.pipe_right _0_512
                                        FStar_List.split
                                       in
                                    (match uu____2279 with
                                     | (mlPats,when_clauses) ->
                                         let pat_ty_compat =
                                           match f_ty_opt with
                                           | Some ([],t) -> ok t
                                           | uu____2366 -> false  in
                                         let _0_515 =
                                           Some
                                             (let _0_514 =
                                                resugar_pat
                                                  f.FStar_Syntax_Syntax.fv_qual
                                                  (FStar_Extraction_ML_Syntax.MLP_CTor
                                                     (d, mlPats))
                                                 in
                                              let _0_513 =
                                                FStar_All.pipe_right
                                                  when_clauses
                                                  FStar_List.flatten
                                                 in
                                              (_0_514, _0_513))
                                            in
                                         (g, _0_515, pat_ty_compat))))))
  
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
          let uu____2431 = extract_one_pat disj false g p expected_t  in
          match uu____2431 with
          | (g,Some (x,v),b) -> (g, (x, v), b)
          | uu____2462 -> failwith "Impossible: Unable to translate pattern"
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
            let uu____2512 = extract_one_pat true g p (Some expected_t)  in
            (match uu____2512 with
             | (g,p,b) ->
                 let uu____2535 =
                   FStar_Util.fold_map
                     (fun b  ->
                        fun p  ->
                          let uu____2547 =
                            extract_one_pat true g p (Some expected_t)  in
                          match uu____2547 with
                          | (uu____2559,p,b') -> ((b && b'), p)) b pats
                    in
                 (match uu____2535 with
                  | (b,ps) ->
                      let ps = p :: ps  in
                      let uu____2596 =
                        FStar_All.pipe_right ps
                          (FStar_List.partition
                             (fun uu___134_2624  ->
                                match uu___134_2624 with
                                | (uu____2628,uu____2629::uu____2630) -> true
                                | uu____2633 -> false))
                         in
                      (match uu____2596 with
                       | (ps_when,rest) ->
                           let ps =
                             FStar_All.pipe_right ps_when
                               (FStar_List.map
                                  (fun uu____2681  ->
                                     match uu____2681 with
                                     | (x,whens) ->
                                         let _0_516 = mk_when_clause whens
                                            in
                                         (x, _0_516)))
                              in
                           let res =
                             match rest with
                             | [] -> (g, ps, b)
                             | rest ->
                                 let _0_519 =
                                   let _0_518 =
                                     let _0_517 =
                                       FStar_Extraction_ML_Syntax.MLP_Branch
                                         (FStar_List.map Prims.fst rest)
                                        in
                                     (_0_517, None)  in
                                   _0_518 :: ps  in
                                 (g, _0_519, b)
                              in
                           res)))
        | uu____2732 ->
            let uu____2733 = extract_one_pat false g p (Some expected_t)  in
            (match uu____2733 with
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
            | FStar_Extraction_ML_Syntax.MLTY_Fun (t0,uu____2815,t1) ->
                let x = FStar_Extraction_ML_Syntax.gensym ()  in
                let _0_522 =
                  let _0_521 =
                    let _0_520 =
                      FStar_All.pipe_left
                        (FStar_Extraction_ML_Syntax.with_ty t0)
                        (FStar_Extraction_ML_Syntax.MLE_Var x)
                       in
                    ((x, t0), _0_520)  in
                  _0_521 :: more_args  in
                eta_args _0_522 t1
            | FStar_Extraction_ML_Syntax.MLTY_Named (uu____2824,uu____2825)
                -> ((FStar_List.rev more_args), t)
            | uu____2837 -> failwith "Impossible: Head type is not an arrow"
             in
          let as_record qual e =
            match ((e.FStar_Extraction_ML_Syntax.expr), qual) with
            | (FStar_Extraction_ML_Syntax.MLE_CTor (uu____2855,args),Some
               (FStar_Syntax_Syntax.Record_ctor (tyname,fields))) ->
                let path =
                  FStar_List.map FStar_Ident.text_of_id tyname.FStar_Ident.ns
                   in
                let fields = record_fields fields args  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     e.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_Record (path, fields))
            | uu____2874 -> e  in
          let resugar_and_maybe_eta qual e =
            let uu____2887 = eta_args [] residualType  in
            match uu____2887 with
            | (eargs,tres) ->
                (match eargs with
                 | [] ->
                     FStar_Extraction_ML_Util.resugar_exp (as_record qual e)
                 | uu____2915 ->
                     let uu____2921 = FStar_List.unzip eargs  in
                     (match uu____2921 with
                      | (binders,eargs) ->
                          (match e.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_CTor (head,args)
                               ->
                               let body =
                                 let _0_524 =
                                   let _0_523 =
                                     FStar_All.pipe_left
                                       (FStar_Extraction_ML_Syntax.with_ty
                                          tres)
                                       (FStar_Extraction_ML_Syntax.MLE_CTor
                                          (head,
                                            (FStar_List.append args eargs)))
                                      in
                                   FStar_All.pipe_left (as_record qual)
                                     _0_523
                                    in
                                 FStar_All.pipe_left
                                   FStar_Extraction_ML_Util.resugar_exp
                                   _0_524
                                  in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    e.FStar_Extraction_ML_Syntax.mlty)
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    (binders, body))
                           | uu____2949 ->
                               failwith "Impossible: Not a constructor")))
             in
          match ((mlAppExpr.FStar_Extraction_ML_Syntax.expr), qual) with
          | (uu____2951,None ) -> mlAppExpr
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____2954;
                FStar_Extraction_ML_Syntax.loc = uu____2955;_},mle::args),Some
             (FStar_Syntax_Syntax.Record_projector (constrname,f))) ->
              let f =
                FStar_Ident.lid_of_ids
                  (FStar_List.append constrname.FStar_Ident.ns [f])
                 in
              let fn = FStar_Extraction_ML_Util.mlpath_of_lid f  in
              let proj = FStar_Extraction_ML_Syntax.MLE_Proj (mle, fn)  in
              let e =
                match args with
                | [] -> proj
                | uu____2973 ->
                    FStar_Extraction_ML_Syntax.MLE_App
                      (let _0_525 =
                         FStar_All.pipe_left
                           (FStar_Extraction_ML_Syntax.with_ty
                              FStar_Extraction_ML_Syntax.MLTY_Top) proj
                          in
                       (_0_525, args))
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
              let _0_526 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) _0_526
          | (FStar_Extraction_ML_Syntax.MLE_Name mlp,Some
             (FStar_Syntax_Syntax.Data_ctor ))
            |(FStar_Extraction_ML_Syntax.MLE_Name mlp,Some
              (FStar_Syntax_Syntax.Record_ctor _)) ->
              let _0_527 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) _0_527
          | uu____2995 -> mlAppExpr
  
let maybe_downgrade_eff :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.e_tag ->
      FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.e_tag
  =
  fun g  ->
    fun f  ->
      fun t  ->
        let uu____3008 =
          (f = FStar_Extraction_ML_Syntax.E_GHOST) &&
            (type_leq g t FStar_Extraction_ML_Syntax.ml_unit_ty)
           in
        if uu____3008 then FStar_Extraction_ML_Syntax.E_PURE else f
  
let rec term_as_mlexpr :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag *
        FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun t  ->
      let uu____3049 = term_as_mlexpr' g t  in
      match uu____3049 with
      | (e,tag,ty) ->
          let tag = maybe_downgrade_eff g tag ty  in
          (FStar_Extraction_ML_UEnv.debug g
             (fun u  ->
                FStar_Util.print_string
                  (let _0_530 = FStar_Syntax_Print.tag_of_term t  in
                   let _0_529 = FStar_Syntax_Print.term_to_string t  in
                   let _0_528 =
                     FStar_Extraction_ML_Code.string_of_mlty
                       g.FStar_Extraction_ML_UEnv.currentModule ty
                      in
                   FStar_Util.format4
                     "term_as_mlexpr (%s) :  %s has ML type %s and effect %s\n"
                     _0_530 _0_529 _0_528
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
          let uu____3068 = check_term_as_mlexpr' g t f ty  in
          match uu____3068 with
          | (e,t) ->
              let uu____3075 = erase g e t f  in
              (match uu____3075 with | (r,uu____3082,t) -> (r, t))

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
          let uu____3090 = term_as_mlexpr g e0  in
          match uu____3090 with
          | (e,tag,t) ->
              let tag = maybe_downgrade_eff g tag t  in
              if FStar_Extraction_ML_Util.eff_leq tag f
              then let _0_531 = maybe_coerce g e t ty  in (_0_531, ty)
              else err_unexpected_eff e0 f tag

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
             (let _0_534 =
                FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos  in
              let _0_533 = FStar_Syntax_Print.tag_of_term top  in
              let _0_532 = FStar_Syntax_Print.term_to_string top  in
              FStar_Util.format3 "%s: term_as_mlexpr' (%s) :  %s \n" _0_534
                _0_533 _0_532));
      (let t = FStar_Syntax_Subst.compress top  in
       match t.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_unknown 
         |FStar_Syntax_Syntax.Tm_delayed _
          |FStar_Syntax_Syntax.Tm_uvar _|FStar_Syntax_Syntax.Tm_bvar _ ->
           failwith
             (let _0_535 = FStar_Syntax_Print.tag_of_term t  in
              FStar_Util.format1 "Impossible: Unexpected term: %s" _0_535)
       | FStar_Syntax_Syntax.Tm_type _
         |FStar_Syntax_Syntax.Tm_refine _|FStar_Syntax_Syntax.Tm_arrow _ ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Mutable_alloc ))
           ->
           let uu____3130 = term_as_mlexpr' g t  in
           (match uu____3130 with
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
            | uu____3157 -> failwith "impossible")
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,uu____3166)) ->
           let t = FStar_Syntax_Subst.compress t  in
           (match t.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) when
                FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname ->
                let ed =
                  FStar_TypeChecker_Env.get_effect_decl
                    g.FStar_Extraction_ML_UEnv.tcenv m
                   in
                let uu____3190 =
                  let _0_536 =
                    FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                     in
                  FStar_All.pipe_right _0_536 Prims.op_Negation  in
                if uu____3190
                then term_as_mlexpr' g t
                else
                  (let ml_result_ty_1 =
                     term_as_mlty g lb.FStar_Syntax_Syntax.lbtyp  in
                   let uu____3197 =
                     term_as_mlexpr g lb.FStar_Syntax_Syntax.lbdef  in
                   match uu____3197 with
                   | (comp_1,uu____3205,uu____3206) ->
                       let uu____3207 =
                         let k =
                           let _0_539 =
                             let _0_538 =
                               let _0_537 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               FStar_All.pipe_right _0_537
                                 FStar_Syntax_Syntax.mk_binder
                                in
                             [_0_538]  in
                           FStar_Syntax_Util.abs _0_539 body None  in
                         let uu____3216 = term_as_mlexpr g k  in
                         match uu____3216 with
                         | (ml_k,uu____3223,t_k) ->
                             let m_2 =
                               match t_k with
                               | FStar_Extraction_ML_Syntax.MLTY_Fun
                                   (uu____3226,uu____3227,m_2) -> m_2
                               | uu____3229 -> failwith "Impossible"  in
                             (ml_k, m_2)
                          in
                       (match uu____3207 with
                        | (ml_k,ty) ->
                            let bind =
                              let _0_541 =
                                FStar_Extraction_ML_Syntax.MLE_Name
                                  (let _0_540 =
                                     FStar_Extraction_ML_UEnv.monad_op_name
                                       ed "bind"
                                      in
                                   FStar_All.pipe_right _0_540 Prims.fst)
                                 in
                              FStar_All.pipe_left
                                (FStar_Extraction_ML_Syntax.with_ty
                                   FStar_Extraction_ML_Syntax.MLTY_Top)
                                _0_541
                               in
                            let _0_542 =
                              FStar_All.pipe_left
                                (FStar_Extraction_ML_Syntax.with_ty ty)
                                (FStar_Extraction_ML_Syntax.MLE_App
                                   (bind, [comp_1; ml_k]))
                               in
                            (_0_542, FStar_Extraction_ML_Syntax.E_IMPURE, ty)))
            | uu____3239 -> term_as_mlexpr' g t)
       | FStar_Syntax_Syntax.Tm_meta (t,_)|FStar_Syntax_Syntax.Tm_uinst (t,_)
           -> term_as_mlexpr' g t
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____3252 =
             FStar_TypeChecker_TcTerm.type_of_tot_term
               g.FStar_Extraction_ML_UEnv.tcenv t
              in
           (match uu____3252 with
            | (uu____3259,ty,uu____3261) ->
                let ml_ty = term_as_mlty g ty  in
                let _0_546 =
                  let _0_545 =
                    let _0_544 =
                      FStar_Extraction_ML_Util.mlconst_of_const'
                        t.FStar_Syntax_Syntax.pos c
                       in
                    FStar_All.pipe_left
                      (fun _0_543  ->
                         FStar_Extraction_ML_Syntax.MLE_Const _0_543) _0_544
                     in
                  FStar_Extraction_ML_Syntax.with_ty ml_ty _0_545  in
                (_0_546, FStar_Extraction_ML_Syntax.E_PURE, ml_ty))
       | FStar_Syntax_Syntax.Tm_name _|FStar_Syntax_Syntax.Tm_fvar _ ->
           let uu____3265 = is_type g t  in
           if uu____3265
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____3270 = FStar_Extraction_ML_UEnv.lookup_term g t  in
              match uu____3270 with
              | (FStar_Util.Inl uu____3277,uu____3278) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | (FStar_Util.Inr (x,mltys,uu____3297),qual) ->
                  (match mltys with
                   | ([],t) when t = FStar_Extraction_ML_Syntax.ml_unit_ty ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t)
                   | ([],t) ->
                       let _0_547 =
                         maybe_eta_data_and_project_record g qual t x  in
                       (_0_547, FStar_Extraction_ML_Syntax.E_PURE, t)
                   | uu____3320 -> err_uninst g t mltys t))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,copt) ->
           let uu____3349 = FStar_Syntax_Subst.open_term bs body  in
           (match uu____3349 with
            | (bs,body) ->
                let reified_body =
                  reify_body g.FStar_Extraction_ML_UEnv.tcenv body  in
                let uu____3358 = binders_as_ml_binders g bs  in
                (match uu____3358 with
                 | (ml_bs,env) ->
                     let uu____3375 = term_as_mlexpr env body  in
                     (match uu____3375 with
                      | (ml_body,f,t) ->
                          let uu____3385 =
                            FStar_List.fold_right
                              (fun uu____3392  ->
                                 fun uu____3393  ->
                                   match (uu____3392, uu____3393) with
                                   | ((uu____3404,targ),(f,t)) ->
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         (FStar_Extraction_ML_Syntax.MLTY_Fun
                                            (targ, f, t)))) ml_bs (f, t)
                             in
                          (match uu____3385 with
                           | (f,tfun) ->
                               let _0_548 =
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty tfun)
                                   (FStar_Extraction_ML_Syntax.MLE_Fun
                                      (ml_bs, ml_body))
                                  in
                               (_0_548, f, tfun)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.tk = uu____3420;
              FStar_Syntax_Syntax.pos = uu____3421;
              FStar_Syntax_Syntax.vars = uu____3422;_},t::[])
           ->
           let uu____3445 = term_as_mlexpr' g (Prims.fst t)  in
           (match uu____3445 with
            | (ml,e_tag,mlty) ->
                (ml, FStar_Extraction_ML_Syntax.E_PURE, mlty))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____3457);
              FStar_Syntax_Syntax.tk = uu____3458;
              FStar_Syntax_Syntax.pos = uu____3459;
              FStar_Syntax_Syntax.vars = uu____3460;_},t::[])
           ->
           let uu____3483 = term_as_mlexpr' g (Prims.fst t)  in
           (match uu____3483 with
            | (ml,e_tag,mlty) ->
                (ml, FStar_Extraction_ML_Syntax.E_IMPURE, mlty))
       | FStar_Syntax_Syntax.Tm_app (head,args) ->
           let is_total uu___136_3519 =
             match uu___136_3519 with
             | FStar_Util.Inl l -> FStar_Syntax_Util.is_total_lcomp l
             | FStar_Util.Inr (l,flags) ->
                 (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid)
                   ||
                   (FStar_All.pipe_right flags
                      (FStar_List.existsb
                         (fun uu___135_3537  ->
                            match uu___135_3537 with
                            | FStar_Syntax_Syntax.TOTAL  -> true
                            | uu____3538 -> false)))
              in
           let uu____3539 =
             let _0_549 =
               (FStar_Syntax_Subst.compress head).FStar_Syntax_Syntax.n  in
             ((head.FStar_Syntax_Syntax.n), _0_549)  in
           (match uu____3539 with
            | (FStar_Syntax_Syntax.Tm_uvar uu____3545,uu____3546) ->
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
            | (uu____3556,FStar_Syntax_Syntax.Tm_abs (bs,uu____3558,Some lc))
                when is_total lc ->
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
            | uu____3587 ->
                let rec extract_app is_data uu____3615 uu____3616 restArgs =
                  match (uu____3615, uu____3616) with
                  | ((mlhead,mlargs_f),(f,t)) ->
                      (match (restArgs, t) with
                       | ([],uu____3664) ->
                           let evaluation_order_guaranteed =
                             (((FStar_List.length mlargs_f) =
                                 (Prims.parse_int "1"))
                                ||
                                (FStar_Extraction_ML_Util.codegen_fsharp ()))
                               ||
                               (match head.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_fvar fv ->
                                    (FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Syntax_Const.op_And)
                                      ||
                                      (FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Syntax_Const.op_Or)
                                | uu____3678 -> false)
                              in
                           let uu____3679 =
                             if evaluation_order_guaranteed
                             then
                               let _0_550 =
                                 FStar_All.pipe_right
                                   (FStar_List.rev mlargs_f)
                                   (FStar_List.map Prims.fst)
                                  in
                               ([], _0_550)
                             else
                               FStar_List.fold_left
                                 (fun uu____3715  ->
                                    fun uu____3716  ->
                                      match (uu____3715, uu____3716) with
                                      | ((lbs,out_args),(arg,f)) ->
                                          if
                                            (f =
                                               FStar_Extraction_ML_Syntax.E_PURE)
                                              ||
                                              (f =
                                                 FStar_Extraction_ML_Syntax.E_GHOST)
                                          then (lbs, (arg :: out_args))
                                          else
                                            (let x =
                                               FStar_Extraction_ML_Syntax.gensym
                                                 ()
                                                in
                                             let _0_552 =
                                               let _0_551 =
                                                 FStar_All.pipe_left
                                                   (FStar_Extraction_ML_Syntax.with_ty
                                                      arg.FStar_Extraction_ML_Syntax.mlty)
                                                   (FStar_Extraction_ML_Syntax.MLE_Var
                                                      x)
                                                  in
                                               _0_551 :: out_args  in
                                             (((x, arg) :: lbs), _0_552)))
                                 ([], []) mlargs_f
                              in
                           (match uu____3679 with
                            | (lbs,mlargs) ->
                                let app =
                                  let _0_553 =
                                    FStar_All.pipe_left
                                      (FStar_Extraction_ML_Syntax.with_ty t)
                                      (FStar_Extraction_ML_Syntax.MLE_App
                                         (mlhead, mlargs))
                                     in
                                  FStar_All.pipe_left
                                    (maybe_eta_data_and_project_record g
                                       is_data t) _0_553
                                   in
                                let l_app =
                                  FStar_List.fold_right
                                    (fun uu____3801  ->
                                       fun out  ->
                                         match uu____3801 with
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
                       | ((arg,uu____3814)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                          (formal_t,f',t)) when is_type g arg ->
                           let uu____3832 =
                             type_leq g formal_t
                               FStar_Extraction_ML_Syntax.ml_unit_ty
                              in
                           if uu____3832
                           then
                             let _0_555 =
                               let _0_554 =
                                 FStar_Extraction_ML_Util.join
                                   arg.FStar_Syntax_Syntax.pos f f'
                                  in
                               (_0_554, t)  in
                             extract_app is_data
                               (mlhead,
                                 ((FStar_Extraction_ML_Syntax.ml_unit,
                                    FStar_Extraction_ML_Syntax.E_PURE) ::
                                 mlargs_f)) _0_555 rest
                           else
                             failwith
                               (let _0_559 =
                                  FStar_Extraction_ML_Code.string_of_mlexpr
                                    g.FStar_Extraction_ML_UEnv.currentModule
                                    mlhead
                                   in
                                let _0_558 =
                                  FStar_Syntax_Print.term_to_string arg  in
                                let _0_557 =
                                  FStar_Syntax_Print.tag_of_term arg  in
                                let _0_556 =
                                  FStar_Extraction_ML_Code.string_of_mlty
                                    g.FStar_Extraction_ML_UEnv.currentModule
                                    formal_t
                                   in
                                FStar_Util.format4
                                  "Impossible: ill-typed application:\n\thead=%s, arg=%s, tag=%s\n\texpected type unit, got %s"
                                  _0_559 _0_558 _0_557 _0_556)
                       | ((e0,uu____3846)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                          (tExpected,f',t)) ->
                           let r = e0.FStar_Syntax_Syntax.pos  in
                           let uu____3865 = term_as_mlexpr g e0  in
                           (match uu____3865 with
                            | (e0,f0,tInferred) ->
                                let e0 =
                                  maybe_coerce g e0 tInferred tExpected  in
                                let _0_561 =
                                  let _0_560 =
                                    FStar_Extraction_ML_Util.join_l r
                                      [f; f'; f0]
                                     in
                                  (_0_560, t)  in
                                extract_app is_data
                                  (mlhead, ((e0, f0) :: mlargs_f)) _0_561
                                  rest)
                       | uu____3881 ->
                           let uu____3888 =
                             FStar_Extraction_ML_Util.udelta_unfold g t  in
                           (match uu____3888 with
                            | Some t ->
                                extract_app is_data (mlhead, mlargs_f) 
                                  (f, t) restArgs
                            | None  ->
                                err_ill_typed_application g top restArgs t))
                   in
                let extract_app_maybe_projector is_data mlhead uu____3924
                  args =
                  match uu____3924 with
                  | (f,t) ->
                      (match is_data with
                       | Some (FStar_Syntax_Syntax.Record_projector
                           uu____3943) ->
                           let rec remove_implicits args f t =
                             match (args, t) with
                             | ((a0,Some (FStar_Syntax_Syntax.Implicit
                                 uu____3993))::args,FStar_Extraction_ML_Syntax.MLTY_Fun
                                (uu____3995,f',t)) ->
                                 let _0_562 =
                                   FStar_Extraction_ML_Util.join
                                     a0.FStar_Syntax_Syntax.pos f f'
                                    in
                                 remove_implicits args _0_562 t
                             | uu____4020 -> (args, f, t)  in
                           let uu____4035 = remove_implicits args f t  in
                           (match uu____4035 with
                            | (args,f,t) ->
                                extract_app is_data (mlhead, []) (f, t) args)
                       | uu____4068 ->
                           extract_app is_data (mlhead, []) (f, t) args)
                   in
                let uu____4075 = is_type g t  in
                if uu____4075
                then
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
                else
                  (let head = FStar_Syntax_Util.un_uinst head  in
                   match head.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_name _
                     |FStar_Syntax_Syntax.Tm_fvar _ ->
                       let uu____4086 =
                         let uu____4093 =
                           FStar_Extraction_ML_UEnv.lookup_term g head  in
                         match uu____4093 with
                         | (FStar_Util.Inr u,q) -> (u, q)
                         | uu____4126 -> failwith "FIXME Ty"  in
                       (match uu____4086 with
                        | ((head_ml,(vars,t),inst_ok),qual) ->
                            let has_typ_apps =
                              match args with
                              | (a,uu____4155)::uu____4156 -> is_type g a
                              | uu____4170 -> false  in
                            let uu____4176 =
                              match vars with
                              | uu____4193::uu____4194 when
                                  (Prims.op_Negation has_typ_apps) && inst_ok
                                  -> (head_ml, t, args)
                              | uu____4201 ->
                                  let n = FStar_List.length vars  in
                                  if n <= (FStar_List.length args)
                                  then
                                    let uu____4221 =
                                      FStar_Util.first_N n args  in
                                    (match uu____4221 with
                                     | (prefix,rest) ->
                                         let prefixAsMLTypes =
                                           FStar_List.map
                                             (fun uu____4274  ->
                                                match uu____4274 with
                                                | (x,uu____4278) ->
                                                    term_as_mlty g x) prefix
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
                                               let uu___140_4283 = head_ml
                                                  in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (uu___140_4283.FStar_Extraction_ML_Syntax.expr);
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   = t;
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___140_4283.FStar_Extraction_ML_Syntax.loc)
                                               }
                                           | FStar_Extraction_ML_Syntax.MLE_App
                                               (head,{
                                                       FStar_Extraction_ML_Syntax.expr
                                                         =
                                                         FStar_Extraction_ML_Syntax.MLE_Const
                                                         (FStar_Extraction_ML_Syntax.MLC_Unit
                                                         );
                                                       FStar_Extraction_ML_Syntax.mlty
                                                         = uu____4285;
                                                       FStar_Extraction_ML_Syntax.loc
                                                         = uu____4286;_}::[])
                                               ->
                                               FStar_All.pipe_right
                                                 (FStar_Extraction_ML_Syntax.MLE_App
                                                    ((let uu___141_4289 =
                                                        head  in
                                                      {
                                                        FStar_Extraction_ML_Syntax.expr
                                                          =
                                                          (uu___141_4289.FStar_Extraction_ML_Syntax.expr);
                                                        FStar_Extraction_ML_Syntax.mlty
                                                          =
                                                          (FStar_Extraction_ML_Syntax.MLTY_Fun
                                                             (FStar_Extraction_ML_Syntax.ml_unit_ty,
                                                               FStar_Extraction_ML_Syntax.E_PURE,
                                                               t));
                                                        FStar_Extraction_ML_Syntax.loc
                                                          =
                                                          (uu___141_4289.FStar_Extraction_ML_Syntax.loc)
                                                      }),
                                                      [FStar_Extraction_ML_Syntax.ml_unit]))
                                                 (FStar_Extraction_ML_Syntax.with_ty
                                                    t)
                                           | uu____4290 ->
                                               failwith
                                                 "Impossible: Unexpected head term"
                                            in
                                         (head, t, rest))
                                  else err_uninst g head (vars, t) top
                               in
                            (match uu____4176 with
                             | (head_ml,head_t,args) ->
                                 (match args with
                                  | [] ->
                                      let _0_563 =
                                        maybe_eta_data_and_project_record g
                                          qual head_t head_ml
                                         in
                                      (_0_563,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        head_t)
                                  | uu____4328 ->
                                      extract_app_maybe_projector qual
                                        head_ml
                                        (FStar_Extraction_ML_Syntax.E_PURE,
                                          head_t) args)))
                   | uu____4334 ->
                       let uu____4335 = term_as_mlexpr g head  in
                       (match uu____4335 with
                        | (head,f,t) ->
                            extract_app_maybe_projector None head (f, t) args)))
       | FStar_Syntax_Syntax.Tm_ascribed (e0,tc,f) ->
           let t =
             match tc with
             | FStar_Util.Inl t -> term_as_mlty g t
             | FStar_Util.Inr c ->
                 term_as_mlty g (FStar_Syntax_Util.comp_result c)
              in
           let f =
             match f with
             | None  -> failwith "Ascription node with an empty effect label"
             | Some l -> effect_as_etag g l  in
           let uu____4383 = check_term_as_mlexpr g e0 f t  in
           (match uu____4383 with | (e,t) -> (e, f, t))
       | FStar_Syntax_Syntax.Tm_let ((is_rec,lbs),e') ->
           let top_level = FStar_Syntax_Syntax.is_top_level lbs  in
           let uu____4404 =
             if is_rec
             then FStar_Syntax_Subst.open_let_rec lbs e'
             else
               (let uu____4412 = FStar_Syntax_Syntax.is_top_level lbs  in
                if uu____4412
                then (lbs, e')
                else
                  (let lb = FStar_List.hd lbs  in
                   let x =
                     FStar_Syntax_Syntax.freshen_bv
                       (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
                      in
                   let lb =
                     let uu___142_4423 = lb  in
                     {
                       FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                       FStar_Syntax_Syntax.lbunivs =
                         (uu___142_4423.FStar_Syntax_Syntax.lbunivs);
                       FStar_Syntax_Syntax.lbtyp =
                         (uu___142_4423.FStar_Syntax_Syntax.lbtyp);
                       FStar_Syntax_Syntax.lbeff =
                         (uu___142_4423.FStar_Syntax_Syntax.lbeff);
                       FStar_Syntax_Syntax.lbdef =
                         (uu___142_4423.FStar_Syntax_Syntax.lbdef)
                     }  in
                   let e' =
                     FStar_Syntax_Subst.subst
                       [FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x)] e'
                      in
                   ([lb], e')))
              in
           (match uu____4404 with
            | (lbs,e') ->
                let lbs =
                  if top_level
                  then
                    FStar_All.pipe_right lbs
                      (FStar_List.map
                         (fun lb  ->
                            let tcenv =
                              let _0_564 =
                                FStar_Ident.lid_of_path
                                  (FStar_List.append
                                     (Prims.fst
                                        g.FStar_Extraction_ML_UEnv.currentModule)
                                     [Prims.snd
                                        g.FStar_Extraction_ML_UEnv.currentModule])
                                  FStar_Range.dummyRange
                                 in
                              FStar_TypeChecker_Env.set_current_module
                                g.FStar_Extraction_ML_UEnv.tcenv _0_564
                               in
                            FStar_Extraction_ML_UEnv.debug g
                              (fun uu____4443  ->
                                 FStar_Options.set_option "debug_level"
                                   (FStar_Options.List
                                      [FStar_Options.String "Norm";
                                      FStar_Options.String "Extraction"]));
                            (let lbdef =
                               let uu____4447 = FStar_Options.ml_ish ()  in
                               if uu____4447
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
                             let uu___143_4451 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___143_4451.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___143_4451.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___143_4451.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___143_4451.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef
                             })))
                  else lbs  in
                let maybe_generalize uu____4465 =
                  match uu____4465 with
                  | { FStar_Syntax_Syntax.lbname = lbname_;
                      FStar_Syntax_Syntax.lbunivs = uu____4476;
                      FStar_Syntax_Syntax.lbtyp = t;
                      FStar_Syntax_Syntax.lbeff = lbeff;
                      FStar_Syntax_Syntax.lbdef = e;_} ->
                      let f_e = effect_as_etag g lbeff  in
                      let t = FStar_Syntax_Subst.compress t  in
                      (match t.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                           let _0_565 = FStar_List.hd bs  in
                           FStar_All.pipe_right _0_565 (is_type_binder g) ->
                           let uu____4523 = FStar_Syntax_Subst.open_comp bs c
                              in
                           (match uu____4523 with
                            | (bs,c) ->
                                let uu____4537 =
                                  let uu____4542 =
                                    FStar_Util.prefix_until
                                      (fun x  ->
                                         Prims.op_Negation
                                           (is_type_binder g x)) bs
                                     in
                                  match uu____4542 with
                                  | None  ->
                                      (bs, (FStar_Syntax_Util.comp_result c))
                                  | Some (bs,b,rest) ->
                                      let _0_566 =
                                        FStar_Syntax_Util.arrow (b :: rest) c
                                         in
                                      (bs, _0_566)
                                   in
                                (match uu____4537 with
                                 | (tbinders,tbody) ->
                                     let n_tbinders =
                                       FStar_List.length tbinders  in
                                     let e =
                                       let _0_567 = normalize_abs e  in
                                       FStar_All.pipe_right _0_567
                                         FStar_Syntax_Util.unmeta
                                        in
                                     (match e.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Tm_abs
                                          (bs,body,uu____4645) ->
                                          let uu____4668 =
                                            FStar_Syntax_Subst.open_term bs
                                              body
                                             in
                                          (match uu____4668 with
                                           | (bs,body) ->
                                               if
                                                 n_tbinders <=
                                                   (FStar_List.length bs)
                                               then
                                                 let uu____4698 =
                                                   FStar_Util.first_N
                                                     n_tbinders bs
                                                    in
                                                 (match uu____4698 with
                                                  | (targs,rest_args) ->
                                                      let expected_source_ty
                                                        =
                                                        let s =
                                                          FStar_List.map2
                                                            (fun uu____4741 
                                                               ->
                                                               fun uu____4742
                                                                  ->
                                                                 match 
                                                                   (uu____4741,
                                                                    uu____4742)
                                                                 with
                                                                 | ((x,uu____4752),
                                                                    (y,uu____4754))
                                                                    ->
                                                                    FStar_Syntax_Syntax.NT
                                                                    (let _0_568
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    y  in
                                                                    (x,
                                                                    _0_568)))
                                                            tbinders targs
                                                           in
                                                        FStar_Syntax_Subst.subst
                                                          s tbody
                                                         in
                                                      let env =
                                                        FStar_List.fold_left
                                                          (fun env  ->
                                                             fun uu____4763 
                                                               ->
                                                               match uu____4763
                                                               with
                                                               | (a,uu____4767)
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
                                                        let _0_569 =
                                                          FStar_All.pipe_right
                                                            targs
                                                            (FStar_List.map
                                                               (fun
                                                                  uu____4788 
                                                                  ->
                                                                  match uu____4788
                                                                  with
                                                                  | (x,uu____4794)
                                                                    ->
                                                                    FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                                    x))
                                                           in
                                                        (_0_569, expected_t)
                                                         in
                                                      let add_unit =
                                                        match rest_args with
                                                        | [] ->
                                                            Prims.op_Negation
                                                              (is_fstar_value
                                                                 body)
                                                        | uu____4798 -> false
                                                         in
                                                      let rest_args =
                                                        if add_unit
                                                        then unit_binder ::
                                                          rest_args
                                                        else rest_args  in
                                                      let body =
                                                        match rest_args with
                                                        | [] -> body
                                                        | uu____4807 ->
                                                            FStar_Syntax_Util.abs
                                                              rest_args body
                                                              None
                                                         in
                                                      (lbname_, f_e,
                                                        (t,
                                                          (targs, polytype)),
                                                        add_unit, body))
                                               else
                                                 failwith
                                                   "Not enough type binders")
                                      | FStar_Syntax_Syntax.Tm_uinst _
                                        |FStar_Syntax_Syntax.Tm_fvar _
                                         |FStar_Syntax_Syntax.Tm_name _ ->
                                          let env =
                                            FStar_List.fold_left
                                              (fun env  ->
                                                 fun uu____4863  ->
                                                   match uu____4863 with
                                                   | (a,uu____4867) ->
                                                       FStar_Extraction_ML_UEnv.extend_ty
                                                         env a None) g
                                              tbinders
                                             in
                                          let expected_t =
                                            term_as_mlty env tbody  in
                                          let polytype =
                                            let _0_570 =
                                              FStar_All.pipe_right tbinders
                                                (FStar_List.map
                                                   (fun uu____4885  ->
                                                      match uu____4885 with
                                                      | (x,uu____4891) ->
                                                          FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                            x))
                                               in
                                            (_0_570, expected_t)  in
                                          let args =
                                            FStar_All.pipe_right tbinders
                                              (FStar_List.map
                                                 (fun uu____4897  ->
                                                    match uu____4897 with
                                                    | (bv,uu____4901) ->
                                                        let _0_571 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            bv
                                                           in
                                                        FStar_All.pipe_right
                                                          _0_571
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
                                      | uu____4939 -> err_value_restriction e)))
                       | uu____4949 ->
                           let expected_t = term_as_mlty g t  in
                           (lbname_, f_e, (t, ([], ([], expected_t))), false,
                             e))
                   in
                let check_lb env uu____5006 =
                  match uu____5006 with
                  | (nm,(lbname,f,(t,(targs,polytype)),add_unit,e)) ->
                      let env =
                        FStar_List.fold_left
                          (fun env  ->
                             fun uu____5077  ->
                               match uu____5077 with
                               | (a,uu____5081) ->
                                   FStar_Extraction_ML_UEnv.extend_ty env a
                                     None) env targs
                         in
                      let expected_t =
                        if add_unit
                        then
                          FStar_Extraction_ML_Syntax.MLTY_Fun
                            (FStar_Extraction_ML_Syntax.ml_unit_ty,
                              FStar_Extraction_ML_Syntax.E_PURE,
                              (Prims.snd polytype))
                        else Prims.snd polytype  in
                      let uu____5084 =
                        check_term_as_mlexpr env e f expected_t  in
                      (match uu____5084 with
                       | (e,uu____5090) ->
                           let f = maybe_downgrade_eff env f expected_t  in
                           (f,
                             {
                               FStar_Extraction_ML_Syntax.mllb_name = nm;
                               FStar_Extraction_ML_Syntax.mllb_tysc =
                                 (Some polytype);
                               FStar_Extraction_ML_Syntax.mllb_add_unit =
                                 add_unit;
                               FStar_Extraction_ML_Syntax.mllb_def = e;
                               FStar_Extraction_ML_Syntax.print_typ = true
                             }))
                   in
                let lbs =
                  FStar_All.pipe_right lbs (FStar_List.map maybe_generalize)
                   in
                let uu____5125 =
                  FStar_List.fold_right
                    (fun lb  ->
                       fun uu____5164  ->
                         match uu____5164 with
                         | (env,lbs) ->
                             let uu____5228 = lb  in
                             (match uu____5228 with
                              | (lbname,uu____5253,(t,(uu____5255,polytype)),add_unit,uu____5258)
                                  ->
                                  let uu____5265 =
                                    FStar_Extraction_ML_UEnv.extend_lb env
                                      lbname t polytype add_unit true
                                     in
                                  (match uu____5265 with
                                   | (env,nm) -> (env, ((nm, lb) :: lbs)))))
                    lbs (g, [])
                   in
                (match uu____5125 with
                 | (env_body,lbs) ->
                     let env_def = if is_rec then env_body else g  in
                     let lbs =
                       FStar_All.pipe_right lbs
                         (FStar_List.map (check_lb env_def))
                        in
                     let e'_rng = e'.FStar_Syntax_Syntax.pos  in
                     let uu____5408 = term_as_mlexpr env_body e'  in
                     (match uu____5408 with
                      | (e',f',t') ->
                          let f =
                            let _0_573 =
                              let _0_572 = FStar_List.map Prims.fst lbs  in
                              f' :: _0_572  in
                            FStar_Extraction_ML_Util.join_l e'_rng _0_573  in
                          let is_rec =
                            if is_rec = true
                            then FStar_Extraction_ML_Syntax.Rec
                            else FStar_Extraction_ML_Syntax.NonRec  in
                          let _0_578 =
                            let _0_577 =
                              let _0_575 =
                                let _0_574 = FStar_List.map Prims.snd lbs  in
                                (is_rec, [], _0_574)  in
                              mk_MLE_Let top_level _0_575 e'  in
                            let _0_576 =
                              FStar_Extraction_ML_Util.mlloc_of_range
                                t.FStar_Syntax_Syntax.pos
                               in
                            FStar_Extraction_ML_Syntax.with_ty_loc t' _0_577
                              _0_576
                             in
                          (_0_578, f, t'))))
       | FStar_Syntax_Syntax.Tm_match (scrutinee,pats) ->
           let uu____5455 = term_as_mlexpr g scrutinee  in
           (match uu____5455 with
            | (e,f_e,t_e) ->
                let uu____5465 = check_pats_for_ite pats  in
                (match uu____5465 with
                 | (b,then_e,else_e) ->
                     let no_lift x t = x  in
                     if b
                     then
                       (match (then_e, else_e) with
                        | (Some then_e,Some else_e) ->
                            let uu____5500 = term_as_mlexpr g then_e  in
                            (match uu____5500 with
                             | (then_mle,f_then,t_then) ->
                                 let uu____5510 = term_as_mlexpr g else_e  in
                                 (match uu____5510 with
                                  | (else_mle,f_else,t_else) ->
                                      let uu____5520 =
                                        let uu____5527 =
                                          type_leq g t_then t_else  in
                                        if uu____5527
                                        then (t_else, no_lift)
                                        else
                                          (let uu____5539 =
                                             type_leq g t_else t_then  in
                                           if uu____5539
                                           then (t_then, no_lift)
                                           else
                                             (FStar_Extraction_ML_Syntax.MLTY_Top,
                                               FStar_Extraction_ML_Syntax.apply_obj_repr))
                                         in
                                      (match uu____5520 with
                                       | (t_branch,maybe_lift) ->
                                           let _0_583 =
                                             let _0_581 =
                                               FStar_Extraction_ML_Syntax.MLE_If
                                                 (let _0_580 =
                                                    maybe_lift then_mle
                                                      t_then
                                                     in
                                                  let _0_579 =
                                                    Some
                                                      (maybe_lift else_mle
                                                         t_else)
                                                     in
                                                  (e, _0_580, _0_579))
                                                in
                                             FStar_All.pipe_left
                                               (FStar_Extraction_ML_Syntax.with_ty
                                                  t_branch) _0_581
                                              in
                                           let _0_582 =
                                             FStar_Extraction_ML_Util.join
                                               then_e.FStar_Syntax_Syntax.pos
                                               f_then f_else
                                              in
                                           (_0_583, _0_582, t_branch))))
                        | uu____5569 ->
                            failwith
                              "ITE pats matched but then and else expressions not found?")
                     else
                       (let uu____5578 =
                          FStar_All.pipe_right pats
                            (FStar_Util.fold_map
                               (fun compat  ->
                                  fun br  ->
                                    let uu____5628 =
                                      FStar_Syntax_Subst.open_branch br  in
                                    match uu____5628 with
                                    | (pat,when_opt,branch) ->
                                        let uu____5658 =
                                          extract_pat g pat t_e  in
                                        (match uu____5658 with
                                         | (env,p,pat_t_compat) ->
                                             let uu____5689 =
                                               match when_opt with
                                               | None  ->
                                                   (None,
                                                     FStar_Extraction_ML_Syntax.E_PURE)
                                               | Some w ->
                                                   let uu____5704 =
                                                     term_as_mlexpr env w  in
                                                   (match uu____5704 with
                                                    | (w,f_w,t_w) ->
                                                        let w =
                                                          maybe_coerce env w
                                                            t_w
                                                            FStar_Extraction_ML_Syntax.ml_bool_ty
                                                           in
                                                        ((Some w), f_w))
                                                in
                                             (match uu____5689 with
                                              | (when_opt,f_when) ->
                                                  let uu____5732 =
                                                    term_as_mlexpr env branch
                                                     in
                                                  (match uu____5732 with
                                                   | (mlbranch,f_branch,t_branch)
                                                       ->
                                                       let _0_584 =
                                                         FStar_All.pipe_right
                                                           p
                                                           (FStar_List.map
                                                              (fun uu____5787
                                                                  ->
                                                                 match uu____5787
                                                                 with
                                                                 | (p,wopt)
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
                                                         _0_584))))) true)
                           in
                        match uu____5578 with
                        | (pat_t_compat,mlbranches) ->
                            let mlbranches = FStar_List.flatten mlbranches
                               in
                            let e =
                              if pat_t_compat
                              then e
                              else
                                (FStar_Extraction_ML_UEnv.debug g
                                   (fun uu____5863  ->
                                      let _0_586 =
                                        FStar_Extraction_ML_Code.string_of_mlexpr
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          e
                                         in
                                      let _0_585 =
                                        FStar_Extraction_ML_Code.string_of_mlty
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          t_e
                                         in
                                      FStar_Util.print2
                                        "Coercing scrutinee %s from type %s because pattern type is incompatible\n"
                                        _0_586 _0_585);
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty t_e)
                                   (FStar_Extraction_ML_Syntax.MLE_Coerce
                                      (e, t_e,
                                        FStar_Extraction_ML_Syntax.MLTY_Top)))
                               in
                            (match mlbranches with
                             | [] ->
                                 let uu____5876 =
                                   let _0_588 =
                                     let _0_587 =
                                       FStar_Syntax_Syntax.lid_as_fv
                                         FStar_Syntax_Const.failwith_lid
                                         FStar_Syntax_Syntax.Delta_constant
                                         None
                                        in
                                     FStar_Extraction_ML_UEnv.lookup_fv g
                                       _0_587
                                      in
                                   FStar_All.pipe_left FStar_Util.right
                                     _0_588
                                    in
                                 (match uu____5876 with
                                  | (fw,uu____5899,uu____5900) ->
                                      let _0_592 =
                                        let _0_591 =
                                          FStar_Extraction_ML_Syntax.MLE_App
                                            (let _0_590 =
                                               let _0_589 =
                                                 FStar_All.pipe_left
                                                   (FStar_Extraction_ML_Syntax.with_ty
                                                      FStar_Extraction_ML_Syntax.ml_string_ty)
                                                   (FStar_Extraction_ML_Syntax.MLE_Const
                                                      (FStar_Extraction_ML_Syntax.MLC_String
                                                         "unreachable"))
                                                  in
                                               [_0_589]  in
                                             (fw, _0_590))
                                           in
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             FStar_Extraction_ML_Syntax.ml_unit_ty)
                                          _0_591
                                         in
                                      (_0_592,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        FStar_Extraction_ML_Syntax.ml_unit_ty))
                             | (uu____5902,uu____5903,(uu____5904,f_first,t_first))::rest
                                 ->
                                 let uu____5936 =
                                   FStar_List.fold_left
                                     (fun uu____5952  ->
                                        fun uu____5953  ->
                                          match (uu____5952, uu____5953) with
                                          | ((topt,f),(uu____5983,uu____5984,
                                                       (uu____5985,f_branch,t_branch)))
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
                                                    let uu____6016 =
                                                      type_leq g t t_branch
                                                       in
                                                    if uu____6016
                                                    then Some t_branch
                                                    else
                                                      (let uu____6019 =
                                                         type_leq g t_branch
                                                           t
                                                          in
                                                       if uu____6019
                                                       then Some t
                                                       else None)
                                                 in
                                              (topt, f))
                                     ((Some t_first), f_first) rest
                                    in
                                 (match uu____5936 with
                                  | (topt,f_match) ->
                                      let mlbranches =
                                        FStar_All.pipe_right mlbranches
                                          (FStar_List.map
                                             (fun uu____6065  ->
                                                match uu____6065 with
                                                | (p,(wopt,uu____6081),
                                                   (b,uu____6083,t)) ->
                                                    let b =
                                                      match topt with
                                                      | None  ->
                                                          FStar_Extraction_ML_Syntax.apply_obj_repr
                                                            b t
                                                      | Some uu____6094 -> b
                                                       in
                                                    (p, wopt, b)))
                                         in
                                      let t_match =
                                        match topt with
                                        | None  ->
                                            FStar_Extraction_ML_Syntax.MLTY_Top
                                        | Some t -> t  in
                                      let _0_593 =
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             t_match)
                                          (FStar_Extraction_ML_Syntax.MLE_Match
                                             (e, mlbranches))
                                         in
                                      (_0_593, f_match, t_match)))))))

let fresh : Prims.string -> (Prims.string * Prims.int) =
  let c = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun x  -> FStar_Util.incr c; (let _0_594 = FStar_ST.read c  in (x, _0_594)) 
let ind_discriminator_body :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlmodule1
  =
  fun env  ->
    fun discName  ->
      fun constrName  ->
        let uu____6126 =
          FStar_TypeChecker_Env.lookup_lid env.FStar_Extraction_ML_UEnv.tcenv
            discName
           in
        match uu____6126 with
        | (uu____6129,fstar_disc_type) ->
            let wildcards =
              let uu____6137 =
                (FStar_Syntax_Subst.compress fstar_disc_type).FStar_Syntax_Syntax.n
                 in
              match uu____6137 with
              | FStar_Syntax_Syntax.Tm_arrow (binders,uu____6144) ->
                  let _0_596 =
                    FStar_All.pipe_right binders
                      (FStar_List.filter
                         (fun uu___137_6174  ->
                            match uu___137_6174 with
                            | (uu____6178,Some (FStar_Syntax_Syntax.Implicit
                               uu____6179)) -> true
                            | uu____6181 -> false))
                     in
                  FStar_All.pipe_right _0_596
                    (FStar_List.map
                       (fun uu____6192  ->
                          let _0_595 = fresh "_"  in
                          (_0_595, FStar_Extraction_ML_Syntax.MLTY_Top)))
              | uu____6198 -> failwith "Discriminator must be a function"  in
            let mlid = fresh "_discr_"  in
            let targ = FStar_Extraction_ML_Syntax.MLTY_Top  in
            let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top  in
            let discrBody =
              let _0_610 =
                FStar_Extraction_ML_Syntax.MLE_Fun
                  (let _0_609 =
                     let _0_608 =
                       FStar_Extraction_ML_Syntax.MLE_Match
                         (let _0_607 =
                            let _0_598 =
                              FStar_Extraction_ML_Syntax.MLE_Name
                                (let _0_597 =
                                   FStar_Extraction_ML_Syntax.idsym mlid  in
                                 ([], _0_597))
                               in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty targ)
                              _0_598
                             in
                          let _0_606 =
                            let _0_605 =
                              let _0_601 =
                                FStar_Extraction_ML_Syntax.MLP_CTor
                                  (let _0_599 =
                                     FStar_Extraction_ML_Syntax.mlpath_of_lident
                                       constrName
                                      in
                                   (_0_599,
                                     [FStar_Extraction_ML_Syntax.MLP_Wild]))
                                 in
                              let _0_600 =
                                FStar_All.pipe_left
                                  (FStar_Extraction_ML_Syntax.with_ty
                                     FStar_Extraction_ML_Syntax.ml_bool_ty)
                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                     (FStar_Extraction_ML_Syntax.MLC_Bool
                                        true))
                                 in
                              (_0_601, None, _0_600)  in
                            let _0_604 =
                              let _0_603 =
                                let _0_602 =
                                  FStar_All.pipe_left
                                    (FStar_Extraction_ML_Syntax.with_ty
                                       FStar_Extraction_ML_Syntax.ml_bool_ty)
                                    (FStar_Extraction_ML_Syntax.MLE_Const
                                       (FStar_Extraction_ML_Syntax.MLC_Bool
                                          false))
                                   in
                                (FStar_Extraction_ML_Syntax.MLP_Wild, None,
                                  _0_602)
                                 in
                              [_0_603]  in
                            _0_605 :: _0_604  in
                          (_0_607, _0_606))
                        in
                     FStar_All.pipe_left
                       (FStar_Extraction_ML_Syntax.with_ty
                          FStar_Extraction_ML_Syntax.ml_bool_ty) _0_608
                      in
                   ((FStar_List.append wildcards [(mlid, targ)]), _0_609))
                 in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty disc_ty) _0_610
               in
            FStar_Extraction_ML_Syntax.MLM_Let
              (let _0_613 =
                 let _0_612 =
                   let _0_611 =
                     FStar_Extraction_ML_UEnv.convIdent
                       discName.FStar_Ident.ident
                      in
                   {
                     FStar_Extraction_ML_Syntax.mllb_name = _0_611;
                     FStar_Extraction_ML_Syntax.mllb_tysc = None;
                     FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                     FStar_Extraction_ML_Syntax.mllb_def = discrBody;
                     FStar_Extraction_ML_Syntax.print_typ = false
                   }  in
                 [_0_612]  in
               (FStar_Extraction_ML_Syntax.NonRec, [], _0_613))
  