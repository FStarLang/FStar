open Prims
exception Un_extractable
let uu___is_Un_extractable: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Un_extractable  -> true | uu____4 -> false
let type_leq:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlty -> Prims.bool
  =
  fun g  ->
    fun t1  ->
      fun t2  ->
        FStar_Extraction_ML_Util.type_leq
          (FStar_Extraction_ML_Util.udelta_unfold g) t1 t2
let type_leq_c:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.mlexpr Prims.option ->
      FStar_Extraction_ML_Syntax.mlty ->
        FStar_Extraction_ML_Syntax.mlty ->
          (Prims.bool* FStar_Extraction_ML_Syntax.mlexpr Prims.option)
  =
  fun g  ->
    fun t1  ->
      fun t2  ->
        FStar_Extraction_ML_Util.type_leq_c
          (FStar_Extraction_ML_Util.udelta_unfold g) t1 t2
let erasableType:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.mlty -> Prims.bool
  =
  fun g  ->
    fun t  ->
      FStar_Extraction_ML_Util.erasableType
        (FStar_Extraction_ML_Util.udelta_unfold g) t
let eraseTypeDeep:
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
  (let _0_474 =
     let _0_473 = FStar_Range.string_of_range r in
     FStar_Util.format2 "%s: %s\n" _0_473 msg in
   FStar_All.pipe_left FStar_Util.print_string _0_474);
  failwith msg
let err_uninst env t uu____105 app =
  match uu____105 with
  | (vars,ty) ->
      let _0_480 =
        let _0_479 = FStar_Syntax_Print.term_to_string t in
        let _0_478 =
          let _0_475 = FStar_All.pipe_right vars (FStar_List.map Prims.fst) in
          FStar_All.pipe_right _0_475 (FStar_String.concat ", ") in
        let _0_477 =
          FStar_Extraction_ML_Code.string_of_mlty
            env.FStar_Extraction_ML_UEnv.currentModule ty in
        let _0_476 = FStar_Syntax_Print.term_to_string app in
        FStar_Util.format4
          "Variable %s has a polymorphic type (forall %s. %s); expected it to be fully instantiated, but got %s"
          _0_479 _0_478 _0_477 _0_476 in
      fail t.FStar_Syntax_Syntax.pos _0_480
let err_ill_typed_application env t args ty =
  let _0_485 =
    let _0_484 = FStar_Syntax_Print.term_to_string t in
    let _0_483 =
      let _0_481 =
        FStar_All.pipe_right args
          (FStar_List.map
             (fun uu____164  ->
                match uu____164 with
                | (x,uu____168) -> FStar_Syntax_Print.term_to_string x)) in
      FStar_All.pipe_right _0_481 (FStar_String.concat " ") in
    let _0_482 =
      FStar_Extraction_ML_Code.string_of_mlty
        env.FStar_Extraction_ML_UEnv.currentModule ty in
    FStar_Util.format3
      "Ill-typed application: application is %s \n remaining args are %s\nml type of head is %s\n"
      _0_484 _0_483 _0_482 in
  fail t.FStar_Syntax_Syntax.pos _0_485
let err_value_restriction t =
  let _0_488 =
    let _0_487 = FStar_Syntax_Print.tag_of_term t in
    let _0_486 = FStar_Syntax_Print.term_to_string t in
    FStar_Util.format2
      "Refusing to generalize because of the value restriction: (%s) %s"
      _0_487 _0_486 in
  fail t.FStar_Syntax_Syntax.pos _0_488
let err_unexpected_eff t f0 f1 =
  let _0_490 =
    let _0_489 = FStar_Syntax_Print.term_to_string t in
    FStar_Util.format3 "for expression %s, Expected effect %s; got effect %s"
      _0_489 (FStar_Extraction_ML_Util.eff_to_string f0)
      (FStar_Extraction_ML_Util.eff_to_string f1) in
  fail t.FStar_Syntax_Syntax.pos _0_490
let effect_as_etag:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Ident.lident -> FStar_Extraction_ML_Syntax.e_tag
  =
  let cache = FStar_Util.smap_create (Prims.parse_int "20") in
  let rec delta_norm_eff g l =
    let uu____214 = FStar_Util.smap_try_find cache l.FStar_Ident.str in
    match uu____214 with
    | Some l -> l
    | None  ->
        let res =
          let uu____218 =
            FStar_TypeChecker_Env.lookup_effect_abbrev
              g.FStar_Extraction_ML_UEnv.tcenv [FStar_Syntax_Syntax.U_zero] l in
          match uu____218 with
          | None  -> l
          | Some (uu____224,c) ->
              delta_norm_eff g (FStar_Syntax_Util.comp_effect_name c) in
        (FStar_Util.smap_add cache l.FStar_Ident.str res; res) in
  fun g  ->
    fun l  ->
      let l = delta_norm_eff g l in
      if FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid
      then FStar_Extraction_ML_Syntax.E_PURE
      else
        if FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GHOST_lid
        then FStar_Extraction_ML_Syntax.E_GHOST
        else FStar_Extraction_ML_Syntax.E_IMPURE
let rec is_arity:
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let t = FStar_Syntax_Util.unmeta t in
      let uu____241 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n in
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
              env.FStar_Extraction_ML_UEnv.tcenv t in
          let uu____264 =
            (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n in
          (match uu____264 with
           | FStar_Syntax_Syntax.Tm_fvar uu____265 -> false
           | uu____266 -> is_arity env t)
      | FStar_Syntax_Syntax.Tm_app uu____267 ->
          let uu____277 = FStar_Syntax_Util.head_and_args t in
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
let rec is_type_aux:
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let t = FStar_Syntax_Subst.compress t in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed _|FStar_Syntax_Syntax.Tm_unknown  ->
          failwith
            (let _0_491 = FStar_Syntax_Print.tag_of_term t in
             FStar_Util.format1 "Impossible: %s" _0_491)
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
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          if uu____432
          then true
          else
            (let uu____438 =
               FStar_TypeChecker_Env.lookup_lid
                 env.FStar_Extraction_ML_UEnv.tcenv
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
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
let is_type:
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let b = is_type_aux env t in
      FStar_Extraction_ML_UEnv.debug env
        (fun uu____638  ->
           if b
           then
             let _0_493 = FStar_Syntax_Print.term_to_string t in
             let _0_492 = FStar_Syntax_Print.tag_of_term t in
             FStar_Util.print2 "is_type %s (%s)\n" _0_493 _0_492
           else
             (let _0_495 = FStar_Syntax_Print.term_to_string t in
              let _0_494 = FStar_Syntax_Print.tag_of_term t in
              FStar_Util.print2 "not a type %s (%s)\n" _0_495 _0_494));
      b
let is_type_binder env x =
  is_arity env (Prims.fst x).FStar_Syntax_Syntax.sort
let is_constructor: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____659 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n in
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
let rec is_fstar_value: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____669 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n in
    match uu____669 with
    | FStar_Syntax_Syntax.Tm_constant _
      |FStar_Syntax_Syntax.Tm_bvar _
       |FStar_Syntax_Syntax.Tm_fvar _|FStar_Syntax_Syntax.Tm_abs _ -> true
    | FStar_Syntax_Syntax.Tm_app (head,args) ->
        let uu____690 = is_constructor head in
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
let rec is_ml_value: FStar_Extraction_ML_Syntax.mlexpr -> Prims.bool =
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
let normalize_abs: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t0  ->
    let rec aux bs t copt =
      let t = FStar_Syntax_Subst.compress t in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_abs (bs',body,copt) ->
          aux (FStar_List.append bs bs') body copt
      | uu____813 ->
          let e' = FStar_Syntax_Util.unascribe t in
          let uu____815 = FStar_Syntax_Util.is_fun e' in
          if uu____815
          then aux bs e' copt
          else FStar_Syntax_Util.abs bs e' copt in
    aux [] t0 None
let unit_binder: FStar_Syntax_Syntax.binder =
  let _0_496 =
    FStar_Syntax_Syntax.new_bv None FStar_TypeChecker_Common.t_unit in
  FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder _0_496
let check_pats_for_ite:
  (FStar_Syntax_Syntax.pat* FStar_Syntax_Syntax.term Prims.option*
    FStar_Syntax_Syntax.term) Prims.list ->
    (Prims.bool* FStar_Syntax_Syntax.term Prims.option*
      FStar_Syntax_Syntax.term Prims.option)
  =
  fun l  ->
    let def = (false, None, None) in
    if (FStar_List.length l) <> (Prims.parse_int "2")
    then def
    else
      (let uu____867 = FStar_List.hd l in
       match uu____867 with
       | (p1,w1,e1) ->
           let uu____886 = FStar_List.hd (FStar_List.tl l) in
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
let instantiate:
  FStar_Extraction_ML_Syntax.mltyscheme ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty
  = fun s  -> fun args  -> FStar_Extraction_ML_Util.subst s args
let erasable:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.e_tag ->
      FStar_Extraction_ML_Syntax.mlty -> Prims.bool
  =
  fun g  ->
    fun f  ->
      fun t  ->
        (f = FStar_Extraction_ML_Syntax.E_GHOST) ||
          ((f = FStar_Extraction_ML_Syntax.E_PURE) && (erasableType g t))
let erase:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.mlexpr ->
      FStar_Extraction_ML_Syntax.mlty ->
        FStar_Extraction_ML_Syntax.e_tag ->
          (FStar_Extraction_ML_Syntax.mlexpr*
            FStar_Extraction_ML_Syntax.e_tag*
            FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun e  ->
      fun ty  ->
        fun f  ->
          let e =
            let uu____967 = erasable g f ty in
            if uu____967
            then
              let uu____968 =
                type_leq g ty FStar_Extraction_ML_Syntax.ml_unit_ty in
              (if uu____968
               then FStar_Extraction_ML_Syntax.ml_unit
               else
                 FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty)
                   (FStar_Extraction_ML_Syntax.MLE_Coerce
                      (FStar_Extraction_ML_Syntax.ml_unit,
                        FStar_Extraction_ML_Syntax.ml_unit_ty, ty)))
            else e in
          (e, f, ty)
let maybe_coerce:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.mlexpr ->
      FStar_Extraction_ML_Syntax.mlty ->
        FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlexpr
  =
  fun g  ->
    fun e  ->
      fun ty  ->
        fun expect  ->
          let ty = eraseTypeDeep g ty in
          let uu____984 = (type_leq_c g (Some e) ty) expect in
          match uu____984 with
          | (true ,Some e') -> e'
          | uu____990 ->
              (FStar_Extraction_ML_UEnv.debug g
                 (fun uu____995  ->
                    let _0_499 =
                      FStar_Extraction_ML_Code.string_of_mlexpr
                        g.FStar_Extraction_ML_UEnv.currentModule e in
                    let _0_498 =
                      FStar_Extraction_ML_Code.string_of_mlty
                        g.FStar_Extraction_ML_UEnv.currentModule ty in
                    let _0_497 =
                      FStar_Extraction_ML_Code.string_of_mlty
                        g.FStar_Extraction_ML_UEnv.currentModule expect in
                    FStar_Util.print3
                      "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n"
                      _0_499 _0_498 _0_497);
               FStar_All.pipe_left
                 (FStar_Extraction_ML_Syntax.with_ty expect)
                 (FStar_Extraction_ML_Syntax.MLE_Coerce (e, ty, expect)))
let bv_as_mlty:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlty
  =
  fun g  ->
    fun bv  ->
      let uu____1002 = FStar_Extraction_ML_UEnv.lookup_bv g bv in
      match uu____1002 with
      | FStar_Util.Inl (uu____1003,t) -> t
      | uu____1010 -> FStar_Extraction_ML_Syntax.MLTY_Top
let rec term_as_mlty:
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
          g.FStar_Extraction_ML_UEnv.tcenv t0 in
      let mlt = term_as_mlty' g t in
      let uu____1044 =
        (fun t  ->
           match t with
           | FStar_Extraction_ML_Syntax.MLTY_Top  -> true
           | FStar_Extraction_ML_Syntax.MLTY_Named uu____1046 ->
               let uu____1050 = FStar_Extraction_ML_Util.udelta_unfold g t in
               (match uu____1050 with
                | None  -> false
                | Some t ->
                    (let rec is_top_ty t =
                       match t with
                       | FStar_Extraction_ML_Syntax.MLTY_Top  -> true
                       | FStar_Extraction_ML_Syntax.MLTY_Named uu____1057 ->
                           let uu____1061 =
                             FStar_Extraction_ML_Util.udelta_unfold g t in
                           (match uu____1061 with
                            | None  -> false
                            | Some t -> is_top_ty t)
                       | uu____1064 -> false in
                     is_top_ty) t)
           | uu____1065 -> false) mlt in
      if uu____1044
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
            g.FStar_Extraction_ML_UEnv.tcenv t0 in
        term_as_mlty' g t
      else mlt
and term_as_mlty':
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlty
  =
  fun env  ->
    fun t  ->
      let t = FStar_Syntax_Subst.compress t in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_bvar _
        |FStar_Syntax_Syntax.Tm_delayed _|FStar_Syntax_Syntax.Tm_unknown  ->
          failwith
            (let _0_500 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format1 "Impossible: Unexpected term %s" _0_500)
      | FStar_Syntax_Syntax.Tm_constant uu____1073 ->
          FStar_Extraction_ML_UEnv.unknownType
      | FStar_Syntax_Syntax.Tm_uvar uu____1074 ->
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
          let uu____1132 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____1132 with
           | (bs,c) ->
               let uu____1137 = binders_as_ml_binders env bs in
               (match uu____1137 with
                | (mlbs,env) ->
                    let t_ret =
                      let eff =
                        FStar_TypeChecker_Env.norm_eff_name
                          env.FStar_Extraction_ML_UEnv.tcenv
                          (FStar_Syntax_Util.comp_effect_name c) in
                      let ed =
                        FStar_TypeChecker_Env.get_effect_decl
                          env.FStar_Extraction_ML_UEnv.tcenv eff in
                      let uu____1154 =
                        FStar_All.pipe_right
                          ed.FStar_Syntax_Syntax.qualifiers
                          (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
                      if uu____1154
                      then
                        let t =
                          FStar_TypeChecker_Util.reify_comp
                            env.FStar_Extraction_ML_UEnv.tcenv
                            (FStar_Syntax_Util.lcomp_of_comp c)
                            FStar_Syntax_Syntax.U_unknown in
                        let res = term_as_mlty' env t in res
                      else
                        term_as_mlty' env (FStar_Syntax_Util.comp_result c) in
                    let erase =
                      effect_as_etag env
                        (FStar_Syntax_Util.comp_effect_name c) in
                    let uu____1160 =
                      FStar_List.fold_right
                        (fun uu____1167  ->
                           fun uu____1168  ->
                             match (uu____1167, uu____1168) with
                             | ((uu____1179,t),(tag,t')) ->
                                 (FStar_Extraction_ML_Syntax.E_PURE,
                                   (FStar_Extraction_ML_Syntax.MLTY_Fun
                                      (t, tag, t')))) mlbs (erase, t_ret) in
                    (match uu____1160 with | (uu____1187,t) -> t)))
      | FStar_Syntax_Syntax.Tm_app (head,args) ->
          let res =
            let uu____1206 =
              (FStar_Syntax_Util.un_uinst head).FStar_Syntax_Syntax.n in
            match uu____1206 with
            | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
            | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv args
            | FStar_Syntax_Syntax.Tm_app (head,args') ->
                let _0_501 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app
                       (head, (FStar_List.append args' args))) None
                    t.FStar_Syntax_Syntax.pos in
                term_as_mlty' env _0_501
            | uu____1244 -> FStar_Extraction_ML_UEnv.unknownType in
          res
      | FStar_Syntax_Syntax.Tm_abs (bs,ty,uu____1247) ->
          let uu____1270 = FStar_Syntax_Subst.open_term bs ty in
          (match uu____1270 with
           | (bs,ty) ->
               let uu____1275 = binders_as_ml_binders env bs in
               (match uu____1275 with | (bts,env) -> term_as_mlty' env ty))
      | FStar_Syntax_Syntax.Tm_type _
        |FStar_Syntax_Syntax.Tm_let _|FStar_Syntax_Syntax.Tm_match _ ->
          FStar_Extraction_ML_UEnv.unknownType
and arg_as_mlty:
  FStar_Extraction_ML_UEnv.env ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.aqual) ->
      FStar_Extraction_ML_Syntax.mlty
  =
  fun g  ->
    fun uu____1293  ->
      match uu____1293 with
      | (a,uu____1297) ->
          let uu____1298 = is_type g a in
          if uu____1298
          then term_as_mlty' g a
          else FStar_Extraction_ML_UEnv.erasedContent
and fv_app_as_mlty:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.args -> FStar_Extraction_ML_Syntax.mlty
  =
  fun g  ->
    fun fv  ->
      fun args  ->
        let uu____1303 =
          FStar_Syntax_Util.arrow_formals
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.ty in
        match uu____1303 with
        | (formals,t) ->
            let mlargs = FStar_List.map (arg_as_mlty g) args in
            let mlargs =
              let n_args = FStar_List.length args in
              if (FStar_List.length formals) > n_args
              then
                let uu____1347 = FStar_Util.first_N n_args formals in
                match uu____1347 with
                | (uu____1361,rest) ->
                    let _0_502 =
                      FStar_List.map
                        (fun uu____1377  ->
                           FStar_Extraction_ML_UEnv.erasedContent) rest in
                    FStar_List.append mlargs _0_502
              else mlargs in
            let nm =
              let uu____1382 =
                FStar_Extraction_ML_UEnv.maybe_mangle_type_projector g fv in
              match uu____1382 with
              | Some p -> p
              | None  ->
                  FStar_Extraction_ML_Syntax.mlpath_of_lident
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            FStar_Extraction_ML_Syntax.MLTY_Named (mlargs, nm)
and binders_as_ml_binders:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.binders ->
      ((FStar_Extraction_ML_Syntax.mlident* FStar_Extraction_ML_Syntax.mlty)
        Prims.list* FStar_Extraction_ML_UEnv.env)
  =
  fun g  ->
    fun bs  ->
      let uu____1397 =
        FStar_All.pipe_right bs
          (FStar_List.fold_left
             (fun uu____1421  ->
                fun b  ->
                  match uu____1421 with
                  | (ml_bs,env) ->
                      let uu____1451 = is_type_binder g b in
                      if uu____1451
                      then
                        let b = Prims.fst b in
                        let env =
                          FStar_Extraction_ML_UEnv.extend_ty env b
                            (Some FStar_Extraction_ML_Syntax.MLTY_Top) in
                        let ml_b =
                          let _0_503 =
                            FStar_Extraction_ML_UEnv.bv_as_ml_termvar b in
                          (_0_503, FStar_Extraction_ML_Syntax.ml_unit_ty) in
                        ((ml_b :: ml_bs), env)
                      else
                        (let b = Prims.fst b in
                         let t = term_as_mlty env b.FStar_Syntax_Syntax.sort in
                         let env =
                           FStar_Extraction_ML_UEnv.extend_bv env b ([], t)
                             false false false in
                         let ml_b =
                           let _0_504 =
                             FStar_Extraction_ML_UEnv.bv_as_ml_termvar b in
                           (_0_504, t) in
                         ((ml_b :: ml_bs), env))) ([], g)) in
      match uu____1397 with | (ml_bs,env) -> ((FStar_List.rev ml_bs), env)
let mk_MLE_Seq:
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
      | (FStar_Extraction_ML_Syntax.MLE_Seq es1,uu____1544) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (FStar_List.append es1 [e2])
      | (uu____1546,FStar_Extraction_ML_Syntax.MLE_Seq es2) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (e1 :: es2)
      | uu____1549 -> FStar_Extraction_ML_Syntax.MLE_Seq [e1; e2]
let mk_MLE_Let:
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
                    | uu____1571 when
                        (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
                          =
                          FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr
                        -> body.FStar_Extraction_ML_Syntax.expr
                    | uu____1572 ->
                        mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def
                          body)
             | uu____1573 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body))
        | uu____1575 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body)
let resugar_pat:
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
           | uu____1589 ->
               (match q with
                | Some (FStar_Syntax_Syntax.Record_ctor (ty,fns)) ->
                    let path =
                      FStar_List.map FStar_Ident.text_of_id ty.FStar_Ident.ns in
                    let fs = record_fields fns pats in
                    FStar_Extraction_ML_Syntax.MLP_Record (path, fs)
                | uu____1605 -> p))
      | uu____1607 -> p
let rec extract_one_pat:
  Prims.bool ->
    Prims.bool ->
      FStar_Extraction_ML_UEnv.env ->
        FStar_Syntax_Syntax.pat ->
          FStar_Extraction_ML_Syntax.mlty Prims.option ->
            (FStar_Extraction_ML_UEnv.env*
              (FStar_Extraction_ML_Syntax.mlpattern*
              FStar_Extraction_ML_Syntax.mlexpr Prims.list) Prims.option*
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
                  let ok = type_leq g t t' in
                  (if Prims.op_Negation ok
                   then
                     FStar_Extraction_ML_UEnv.debug g
                       (fun uu____1646  ->
                          let _0_506 =
                            FStar_Extraction_ML_Code.string_of_mlty
                              g.FStar_Extraction_ML_UEnv.currentModule t' in
                          let _0_505 =
                            FStar_Extraction_ML_Code.string_of_mlty
                              g.FStar_Extraction_ML_UEnv.currentModule t in
                          FStar_Util.print2
                            "Expected pattern type %s; got pattern type %s\n"
                            _0_506 _0_505)
                   else ();
                   ok) in
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_disj uu____1655 ->
                failwith "Impossible: Nested disjunctive pattern"
            | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int
                (c,None )) ->
                let i = FStar_Const.Const_int (c, None) in
                let x = FStar_Extraction_ML_Syntax.gensym () in
                let when_clause =
                  let _0_514 =
                    FStar_Extraction_ML_Syntax.MLE_App
                      (let _0_513 =
                         let _0_512 =
                           FStar_All.pipe_left
                             (FStar_Extraction_ML_Syntax.with_ty
                                FStar_Extraction_ML_Syntax.ml_int_ty)
                             (FStar_Extraction_ML_Syntax.MLE_Var x) in
                         let _0_511 =
                           let _0_510 =
                             let _0_509 =
                               let _0_508 =
                                 FStar_Extraction_ML_Util.mlconst_of_const'
                                   p.FStar_Syntax_Syntax.p i in
                               FStar_All.pipe_left
                                 (fun _0_507  ->
                                    FStar_Extraction_ML_Syntax.MLE_Const
                                      _0_507) _0_508 in
                             FStar_All.pipe_left
                               (FStar_Extraction_ML_Syntax.with_ty
                                  FStar_Extraction_ML_Syntax.ml_int_ty)
                               _0_509 in
                           [_0_510] in
                         _0_512 :: _0_511 in
                       (FStar_Extraction_ML_Util.prims_op_equality, _0_513)) in
                  FStar_All.pipe_left
                    (FStar_Extraction_ML_Syntax.with_ty
                       FStar_Extraction_ML_Syntax.ml_bool_ty) _0_514 in
                let _0_515 = ok FStar_Extraction_ML_Syntax.ml_int_ty in
                (g,
                  (Some
                     ((FStar_Extraction_ML_Syntax.MLP_Var x), [when_clause])),
                  _0_515)
            | FStar_Syntax_Syntax.Pat_constant s ->
                let t =
                  FStar_TypeChecker_TcTerm.tc_constant FStar_Range.dummyRange
                    s in
                let mlty = term_as_mlty g t in
                let _0_518 =
                  Some
                    (let _0_516 =
                       FStar_Extraction_ML_Syntax.MLP_Const
                         (FStar_Extraction_ML_Util.mlconst_of_const'
                            p.FStar_Syntax_Syntax.p s) in
                     (_0_516, [])) in
                let _0_517 = ok mlty in (g, _0_518, _0_517)
            | FStar_Syntax_Syntax.Pat_var x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort in
                let g =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp in
                let _0_521 =
                  if imp
                  then None
                  else
                    Some
                      ((let _0_519 =
                          FStar_Extraction_ML_Syntax.MLP_Var
                            (FStar_Extraction_ML_Syntax.bv_as_mlident x) in
                        (_0_519, []))) in
                let _0_520 = ok mlty in (g, _0_521, _0_520)
            | FStar_Syntax_Syntax.Pat_wild x when disjunctive_pat ->
                (g, (Some (FStar_Extraction_ML_Syntax.MLP_Wild, [])), true)
            | FStar_Syntax_Syntax.Pat_wild x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort in
                let g =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp in
                let _0_524 =
                  if imp
                  then None
                  else
                    Some
                      ((let _0_522 =
                          FStar_Extraction_ML_Syntax.MLP_Var
                            (FStar_Extraction_ML_Syntax.bv_as_mlident x) in
                        (_0_522, []))) in
                let _0_523 = ok mlty in (g, _0_524, _0_523)
            | FStar_Syntax_Syntax.Pat_dot_term uu____1749 -> (g, None, true)
            | FStar_Syntax_Syntax.Pat_cons (f,pats) ->
                let uu____1773 =
                  let uu____1776 = FStar_Extraction_ML_UEnv.lookup_fv g f in
                  match uu____1776 with
                  | FStar_Util.Inr
                      ({
                         FStar_Extraction_ML_Syntax.expr =
                           FStar_Extraction_ML_Syntax.MLE_Name n;
                         FStar_Extraction_ML_Syntax.mlty = uu____1780;
                         FStar_Extraction_ML_Syntax.loc = uu____1781;_},ttys,uu____1783)
                      -> (n, ttys)
                  | uu____1789 -> failwith "Expected a constructor" in
                (match uu____1773 with
                 | (d,tys) ->
                     let nTyVars = FStar_List.length (Prims.fst tys) in
                     let uu____1803 = FStar_Util.first_N nTyVars pats in
                     (match uu____1803 with
                      | (tysVarPats,restPats) ->
                          let f_ty_opt =
                            try
                              let mlty_args =
                                FStar_All.pipe_right tysVarPats
                                  (FStar_List.map
                                     (fun uu____1877  ->
                                        match uu____1877 with
                                        | (p,uu____1883) ->
                                            (match p.FStar_Syntax_Syntax.v
                                             with
                                             | FStar_Syntax_Syntax.Pat_dot_term
                                                 (uu____1888,t) ->
                                                 term_as_mlty g t
                                             | uu____1894 ->
                                                 (FStar_Extraction_ML_UEnv.debug
                                                    g
                                                    (fun uu____1896  ->
                                                       let _0_525 =
                                                         FStar_Syntax_Print.pat_to_string
                                                           p in
                                                       FStar_Util.print1
                                                         "Pattern %s is not extractable"
                                                         _0_525);
                                                  Prims.raise Un_extractable)))) in
                              let f_ty =
                                FStar_Extraction_ML_Util.subst tys mlty_args in
                              Some
                                (FStar_Extraction_ML_Util.uncurry_mlty_fun
                                   f_ty)
                            with | Un_extractable  -> None in
                          let uu____1909 =
                            FStar_Util.fold_map
                              (fun g  ->
                                 fun uu____1924  ->
                                   match uu____1924 with
                                   | (p,imp) ->
                                       let uu____1935 =
                                         extract_one_pat disjunctive_pat true
                                           g p None in
                                       (match uu____1935 with
                                        | (g,p,uu____1951) -> (g, p))) g
                              tysVarPats in
                          (match uu____1909 with
                           | (g,tyMLPats) ->
                               let uu____1983 =
                                 FStar_Util.fold_map
                                   (fun uu____2009  ->
                                      fun uu____2010  ->
                                        match (uu____2009, uu____2010) with
                                        | ((g,f_ty_opt),(p,imp)) ->
                                            let uu____2059 =
                                              match f_ty_opt with
                                              | Some (hd::rest,res) ->
                                                  ((Some (rest, res)),
                                                    (Some hd))
                                              | uu____2091 -> (None, None) in
                                            (match uu____2059 with
                                             | (f_ty_opt,expected_ty) ->
                                                 let uu____2128 =
                                                   extract_one_pat
                                                     disjunctive_pat false g
                                                     p expected_ty in
                                                 (match uu____2128 with
                                                  | (g,p,uu____2150) ->
                                                      ((g, f_ty_opt), p))))
                                   (g, f_ty_opt) restPats in
                               (match uu____1983 with
                                | ((g,f_ty_opt),restMLPats) ->
                                    let uu____2211 =
                                      let _0_526 =
                                        FStar_All.pipe_right
                                          (FStar_List.append tyMLPats
                                             restMLPats)
                                          (FStar_List.collect
                                             (fun uu___135_2246  ->
                                                match uu___135_2246 with
                                                | Some x -> [x]
                                                | uu____2268 -> [])) in
                                      FStar_All.pipe_right _0_526
                                        FStar_List.split in
                                    (match uu____2211 with
                                     | (mlPats,when_clauses) ->
                                         let pat_ty_compat =
                                           match f_ty_opt with
                                           | Some ([],t) -> ok t
                                           | uu____2298 -> false in
                                         let _0_529 =
                                           Some
                                             (let _0_528 =
                                                resugar_pat
                                                  f.FStar_Syntax_Syntax.fv_qual
                                                  (FStar_Extraction_ML_Syntax.MLP_CTor
                                                     (d, mlPats)) in
                                              let _0_527 =
                                                FStar_All.pipe_right
                                                  when_clauses
                                                  FStar_List.flatten in
                                              (_0_528, _0_527)) in
                                         (g, _0_529, pat_ty_compat))))))
let extract_pat:
  FStar_Extraction_ML_UEnv.env ->
    (FStar_Syntax_Syntax.pat',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.withinfo_t ->
      FStar_Extraction_ML_Syntax.mlty ->
        (FStar_Extraction_ML_UEnv.env* (FStar_Extraction_ML_Syntax.mlpattern*
          FStar_Extraction_ML_Syntax.mlexpr Prims.option) Prims.list*
          Prims.bool)
  =
  fun g  ->
    fun p  ->
      fun expected_t  ->
        let extract_one_pat disj g p expected_t =
          let uu____2363 = extract_one_pat disj false g p expected_t in
          match uu____2363 with
          | (g,Some (x,v),b) -> (g, (x, v), b)
          | uu____2394 -> failwith "Impossible: Unable to translate pattern" in
        let mk_when_clause whens =
          match whens with
          | [] -> None
          | hd::tl ->
              Some
                (FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd tl) in
        match p.FStar_Syntax_Syntax.v with
        | FStar_Syntax_Syntax.Pat_disj [] ->
            failwith "Impossible: Empty disjunctive pattern"
        | FStar_Syntax_Syntax.Pat_disj (p::pats) ->
            let uu____2444 = extract_one_pat true g p (Some expected_t) in
            (match uu____2444 with
             | (g,p,b) ->
                 let uu____2467 =
                   FStar_Util.fold_map
                     (fun b  ->
                        fun p  ->
                          let uu____2479 =
                            extract_one_pat true g p (Some expected_t) in
                          match uu____2479 with
                          | (uu____2491,p,b') -> ((b && b'), p)) b pats in
                 (match uu____2467 with
                  | (b,ps) ->
                      let ps = p :: ps in
                      let uu____2528 =
                        FStar_All.pipe_right ps
                          (FStar_List.partition
                             (fun uu___136_2556  ->
                                match uu___136_2556 with
                                | (uu____2560,uu____2561::uu____2562) -> true
                                | uu____2565 -> false)) in
                      (match uu____2528 with
                       | (ps_when,rest) ->
                           let ps =
                             FStar_All.pipe_right ps_when
                               (FStar_List.map
                                  (fun uu____2613  ->
                                     match uu____2613 with
                                     | (x,whens) ->
                                         let _0_530 = mk_when_clause whens in
                                         (x, _0_530))) in
                           let res =
                             match rest with
                             | [] -> (g, ps, b)
                             | rest ->
                                 let _0_533 =
                                   let _0_532 =
                                     let _0_531 =
                                       FStar_Extraction_ML_Syntax.MLP_Branch
                                         (FStar_List.map Prims.fst rest) in
                                     (_0_531, None) in
                                   _0_532 :: ps in
                                 (g, _0_533, b) in
                           res)))
        | uu____2664 ->
            let uu____2665 = extract_one_pat false g p (Some expected_t) in
            (match uu____2665 with
             | (g,(p,whens),b) ->
                 let when_clause = mk_when_clause whens in
                 (g, [(p, when_clause)], b))
let maybe_eta_data_and_project_record:
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
                let x = FStar_Extraction_ML_Syntax.gensym () in
                let _0_536 =
                  let _0_535 =
                    let _0_534 =
                      FStar_All.pipe_left
                        (FStar_Extraction_ML_Syntax.with_ty t0)
                        (FStar_Extraction_ML_Syntax.MLE_Var x) in
                    ((x, t0), _0_534) in
                  _0_535 :: more_args in
                eta_args _0_536 t1
            | FStar_Extraction_ML_Syntax.MLTY_Named (uu____2756,uu____2757)
                -> ((FStar_List.rev more_args), t)
            | uu____2769 -> failwith "Impossible: Head type is not an arrow" in
          let as_record qual e =
            match ((e.FStar_Extraction_ML_Syntax.expr), qual) with
            | (FStar_Extraction_ML_Syntax.MLE_CTor (uu____2787,args),Some
               (FStar_Syntax_Syntax.Record_ctor (tyname,fields))) ->
                let path =
                  FStar_List.map FStar_Ident.text_of_id tyname.FStar_Ident.ns in
                let fields = record_fields fields args in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     e.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_Record (path, fields))
            | uu____2806 -> e in
          let resugar_and_maybe_eta qual e =
            let uu____2819 = eta_args [] residualType in
            match uu____2819 with
            | (eargs,tres) ->
                (match eargs with
                 | [] ->
                     FStar_Extraction_ML_Util.resugar_exp (as_record qual e)
                 | uu____2847 ->
                     let uu____2853 = FStar_List.unzip eargs in
                     (match uu____2853 with
                      | (binders,eargs) ->
                          (match e.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_CTor (head,args)
                               ->
                               let body =
                                 let _0_538 =
                                   let _0_537 =
                                     FStar_All.pipe_left
                                       (FStar_Extraction_ML_Syntax.with_ty
                                          tres)
                                       (FStar_Extraction_ML_Syntax.MLE_CTor
                                          (head,
                                            (FStar_List.append args eargs))) in
                                   FStar_All.pipe_left (as_record qual)
                                     _0_537 in
                                 FStar_All.pipe_left
                                   FStar_Extraction_ML_Util.resugar_exp
                                   _0_538 in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    e.FStar_Extraction_ML_Syntax.mlty)
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    (binders, body))
                           | uu____2881 ->
                               failwith "Impossible: Not a constructor"))) in
          match ((mlAppExpr.FStar_Extraction_ML_Syntax.expr), qual) with
          | (uu____2883,None ) -> mlAppExpr
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____2886;
                FStar_Extraction_ML_Syntax.loc = uu____2887;_},mle::args),Some
             (FStar_Syntax_Syntax.Record_projector (constrname,f))) ->
              let f =
                FStar_Ident.lid_of_ids
                  (FStar_List.append constrname.FStar_Ident.ns [f]) in
              let fn = FStar_Extraction_ML_Util.mlpath_of_lid f in
              let proj = FStar_Extraction_ML_Syntax.MLE_Proj (mle, fn) in
              let e =
                match args with
                | [] -> proj
                | uu____2905 ->
                    FStar_Extraction_ML_Syntax.MLE_App
                      (let _0_539 =
                         FStar_All.pipe_left
                           (FStar_Extraction_ML_Syntax.with_ty
                              FStar_Extraction_ML_Syntax.MLTY_Top) proj in
                       (_0_539, args)) in
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
              let _0_540 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs)) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) _0_540
          | (FStar_Extraction_ML_Syntax.MLE_Name mlp,Some
             (FStar_Syntax_Syntax.Data_ctor ))
            |(FStar_Extraction_ML_Syntax.MLE_Name mlp,Some
              (FStar_Syntax_Syntax.Record_ctor _)) ->
              let _0_541 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, [])) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) _0_541
          | uu____2927 -> mlAppExpr
let maybe_downgrade_eff:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.e_tag ->
      FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.e_tag
  =
  fun g  ->
    fun f  ->
      fun t  ->
        let uu____2940 =
          (f = FStar_Extraction_ML_Syntax.E_GHOST) &&
            (type_leq g t FStar_Extraction_ML_Syntax.ml_unit_ty) in
        if uu____2940 then FStar_Extraction_ML_Syntax.E_PURE else f
let rec term_as_mlexpr:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Extraction_ML_Syntax.mlexpr* FStar_Extraction_ML_Syntax.e_tag*
        FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun t  ->
      let uu____2981 = term_as_mlexpr' g t in
      match uu____2981 with
      | (e,tag,ty) ->
          let tag = maybe_downgrade_eff g tag ty in
          (FStar_Extraction_ML_UEnv.debug g
             (fun u  ->
                FStar_Util.print_string
                  (let _0_544 = FStar_Syntax_Print.tag_of_term t in
                   let _0_543 = FStar_Syntax_Print.term_to_string t in
                   let _0_542 =
                     FStar_Extraction_ML_Code.string_of_mlty
                       g.FStar_Extraction_ML_UEnv.currentModule ty in
                   FStar_Util.format4
                     "term_as_mlexpr (%s) :  %s has ML type %s and effect %s\n"
                     _0_544 _0_543 _0_542
                     (FStar_Extraction_ML_Util.eff_to_string tag)));
           erase g e ty tag)
and check_term_as_mlexpr:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Extraction_ML_Syntax.e_tag ->
        FStar_Extraction_ML_Syntax.mlty ->
          (FStar_Extraction_ML_Syntax.mlexpr*
            FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun t  ->
      fun f  ->
        fun ty  ->
          let uu____3000 = check_term_as_mlexpr' g t f ty in
          match uu____3000 with
          | (e,t) ->
              let uu____3007 = erase g e t f in
              (match uu____3007 with | (r,uu____3014,t) -> (r, t))
and check_term_as_mlexpr':
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Extraction_ML_Syntax.e_tag ->
        FStar_Extraction_ML_Syntax.mlty ->
          (FStar_Extraction_ML_Syntax.mlexpr*
            FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun e0  ->
      fun f  ->
        fun ty  ->
          let uu____3022 = term_as_mlexpr g e0 in
          match uu____3022 with
          | (e,tag,t) ->
              let tag = maybe_downgrade_eff g tag t in
              if FStar_Extraction_ML_Util.eff_leq tag f
              then let _0_545 = maybe_coerce g e t ty in (_0_545, ty)
              else err_unexpected_eff e0 f tag
and term_as_mlexpr':
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Extraction_ML_Syntax.mlexpr* FStar_Extraction_ML_Syntax.e_tag*
        FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun top  ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u  ->
           FStar_Util.print_string
             (let _0_548 =
                FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos in
              let _0_547 = FStar_Syntax_Print.tag_of_term top in
              let _0_546 = FStar_Syntax_Print.term_to_string top in
              FStar_Util.format3 "%s: term_as_mlexpr' (%s) :  %s \n" _0_548
                _0_547 _0_546));
      (let t = FStar_Syntax_Subst.compress top in
       match t.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_unknown 
         |FStar_Syntax_Syntax.Tm_delayed _
          |FStar_Syntax_Syntax.Tm_uvar _|FStar_Syntax_Syntax.Tm_bvar _ ->
           failwith
             (let _0_549 = FStar_Syntax_Print.tag_of_term t in
              FStar_Util.format1 "Impossible: Unexpected term: %s" _0_549)
       | FStar_Syntax_Syntax.Tm_type _
         |FStar_Syntax_Syntax.Tm_refine _|FStar_Syntax_Syntax.Tm_arrow _ ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Mutable_alloc ))
           ->
           let uu____3062 = term_as_mlexpr' g t in
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
            | uu____3089 -> failwith "impossible")
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,uu____3098)) ->
           let t = FStar_Syntax_Subst.compress t in
           (match t.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) when
                FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname ->
                let ed =
                  FStar_TypeChecker_Env.get_effect_decl
                    g.FStar_Extraction_ML_UEnv.tcenv m in
                let uu____3122 =
                  let _0_550 =
                    FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
                  FStar_All.pipe_right _0_550 Prims.op_Negation in
                if uu____3122
                then term_as_mlexpr' g t
                else
                  (let ml_result_ty_1 =
                     term_as_mlty g lb.FStar_Syntax_Syntax.lbtyp in
                   let uu____3129 =
                     term_as_mlexpr g lb.FStar_Syntax_Syntax.lbdef in
                   match uu____3129 with
                   | (comp_1,uu____3137,uu____3138) ->
                       let uu____3139 =
                         let k =
                           let _0_553 =
                             let _0_552 =
                               let _0_551 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               FStar_All.pipe_right _0_551
                                 FStar_Syntax_Syntax.mk_binder in
                             [_0_552] in
                           FStar_Syntax_Util.abs _0_553 body None in
                         let uu____3148 = term_as_mlexpr g k in
                         match uu____3148 with
                         | (ml_k,uu____3155,t_k) ->
                             let m_2 =
                               match t_k with
                               | FStar_Extraction_ML_Syntax.MLTY_Fun
                                   (uu____3158,uu____3159,m_2) -> m_2
                               | uu____3161 -> failwith "Impossible" in
                             (ml_k, m_2) in
                       (match uu____3139 with
                        | (ml_k,ty) ->
                            let bind =
                              let _0_555 =
                                FStar_Extraction_ML_Syntax.MLE_Name
                                  (let _0_554 =
                                     FStar_Extraction_ML_UEnv.monad_op_name
                                       ed "bind" in
                                   FStar_All.pipe_right _0_554 Prims.fst) in
                              FStar_All.pipe_left
                                (FStar_Extraction_ML_Syntax.with_ty
                                   FStar_Extraction_ML_Syntax.MLTY_Top)
                                _0_555 in
                            let _0_556 =
                              FStar_All.pipe_left
                                (FStar_Extraction_ML_Syntax.with_ty ty)
                                (FStar_Extraction_ML_Syntax.MLE_App
                                   (bind, [comp_1; ml_k])) in
                            (_0_556, FStar_Extraction_ML_Syntax.E_IMPURE, ty)))
            | uu____3171 -> term_as_mlexpr' g t)
       | FStar_Syntax_Syntax.Tm_meta (t,_)|FStar_Syntax_Syntax.Tm_uinst (t,_)
           -> term_as_mlexpr' g t
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____3184 =
             FStar_TypeChecker_TcTerm.type_of_tot_term
               g.FStar_Extraction_ML_UEnv.tcenv t in
           (match uu____3184 with
            | (uu____3191,ty,uu____3193) ->
                let ml_ty = term_as_mlty g ty in
                let _0_560 =
                  let _0_559 =
                    let _0_558 =
                      FStar_Extraction_ML_Util.mlconst_of_const'
                        t.FStar_Syntax_Syntax.pos c in
                    FStar_All.pipe_left
                      (fun _0_557  ->
                         FStar_Extraction_ML_Syntax.MLE_Const _0_557) _0_558 in
                  FStar_Extraction_ML_Syntax.with_ty ml_ty _0_559 in
                (_0_560, FStar_Extraction_ML_Syntax.E_PURE, ml_ty))
       | FStar_Syntax_Syntax.Tm_name _|FStar_Syntax_Syntax.Tm_fvar _ ->
           let uu____3197 = is_type g t in
           if uu____3197
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____3202 = FStar_Extraction_ML_UEnv.lookup_term g t in
              match uu____3202 with
              | (FStar_Util.Inl uu____3209,uu____3210) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | (FStar_Util.Inr (x,mltys,uu____3229),qual) ->
                  (match mltys with
                   | ([],t) when t = FStar_Extraction_ML_Syntax.ml_unit_ty ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t)
                   | ([],t) ->
                       let _0_561 =
                         maybe_eta_data_and_project_record g qual t x in
                       (_0_561, FStar_Extraction_ML_Syntax.E_PURE, t)
                   | uu____3252 -> err_uninst g t mltys t))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,copt) ->
           let uu____3281 = FStar_Syntax_Subst.open_term bs body in
           (match uu____3281 with
            | (bs,body) ->
                let uu____3289 = binders_as_ml_binders g bs in
                (match uu____3289 with
                 | (ml_bs,env) ->
                     let uu____3306 = term_as_mlexpr env body in
                     (match uu____3306 with
                      | (ml_body,f,t) ->
                          let uu____3316 =
                            FStar_List.fold_right
                              (fun uu____3323  ->
                                 fun uu____3324  ->
                                   match (uu____3323, uu____3324) with
                                   | ((uu____3335,targ),(f,t)) ->
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         (FStar_Extraction_ML_Syntax.MLTY_Fun
                                            (targ, f, t)))) ml_bs (f, t) in
                          (match uu____3316 with
                           | (f,tfun) ->
                               let _0_562 =
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty tfun)
                                   (FStar_Extraction_ML_Syntax.MLE_Fun
                                      (ml_bs, ml_body)) in
                               (_0_562, f, tfun)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.tk = uu____3351;
              FStar_Syntax_Syntax.pos = uu____3352;
              FStar_Syntax_Syntax.vars = uu____3353;_},t::[])
           ->
           let uu____3376 = term_as_mlexpr' g (Prims.fst t) in
           (match uu____3376 with
            | (ml,e_tag,mlty) ->
                (ml, FStar_Extraction_ML_Syntax.E_PURE, mlty))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____3388);
              FStar_Syntax_Syntax.tk = uu____3389;
              FStar_Syntax_Syntax.pos = uu____3390;
              FStar_Syntax_Syntax.vars = uu____3391;_},t::[])
           ->
           let uu____3414 = term_as_mlexpr' g (Prims.fst t) in
           (match uu____3414 with
            | (ml,e_tag,mlty) ->
                (ml, FStar_Extraction_ML_Syntax.E_IMPURE, mlty))
       | FStar_Syntax_Syntax.Tm_app (head,args) ->
           let is_total uu___138_3450 =
             match uu___138_3450 with
             | FStar_Util.Inl l -> FStar_Syntax_Util.is_total_lcomp l
             | FStar_Util.Inr (l,flags) ->
                 (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid)
                   ||
                   (FStar_All.pipe_right flags
                      (FStar_List.existsb
                         (fun uu___137_3468  ->
                            match uu___137_3468 with
                            | FStar_Syntax_Syntax.TOTAL  -> true
                            | uu____3469 -> false))) in
           let uu____3470 =
             let _0_563 =
               (FStar_Syntax_Subst.compress head).FStar_Syntax_Syntax.n in
             ((head.FStar_Syntax_Syntax.n), _0_563) in
           (match uu____3470 with
            | (FStar_Syntax_Syntax.Tm_uvar uu____3476,uu____3477) ->
                let t =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.Iota;
                    FStar_TypeChecker_Normalize.Zeta;
                    FStar_TypeChecker_Normalize.EraseUniverses;
                    FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                    g.FStar_Extraction_ML_UEnv.tcenv t in
                term_as_mlexpr' g t
            | (uu____3487,FStar_Syntax_Syntax.Tm_abs (bs,uu____3489,Some lc))
                when is_total lc ->
                let t =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.Iota;
                    FStar_TypeChecker_Normalize.Zeta;
                    FStar_TypeChecker_Normalize.EraseUniverses;
                    FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                    g.FStar_Extraction_ML_UEnv.tcenv t in
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
                               (match head.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_fvar fv ->
                                    (FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Syntax_Const.op_And)
                                      ||
                                      (FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Syntax_Const.op_Or)
                                | uu____3609 -> false) in
                           let uu____3610 =
                             if evaluation_order_guaranteed
                             then
                               let _0_564 =
                                 FStar_All.pipe_right
                                   (FStar_List.rev mlargs_f)
                                   (FStar_List.map Prims.fst) in
                               ([], _0_564)
                             else
                               FStar_List.fold_left
                                 (fun uu____3646  ->
                                    fun uu____3647  ->
                                      match (uu____3646, uu____3647) with
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
                                                 () in
                                             let _0_566 =
                                               let _0_565 =
                                                 FStar_All.pipe_left
                                                   (FStar_Extraction_ML_Syntax.with_ty
                                                      arg.FStar_Extraction_ML_Syntax.mlty)
                                                   (FStar_Extraction_ML_Syntax.MLE_Var
                                                      x) in
                                               _0_565 :: out_args in
                                             (((x, arg) :: lbs), _0_566)))
                                 ([], []) mlargs_f in
                           (match uu____3610 with
                            | (lbs,mlargs) ->
                                let app =
                                  let _0_567 =
                                    FStar_All.pipe_left
                                      (FStar_Extraction_ML_Syntax.with_ty t)
                                      (FStar_Extraction_ML_Syntax.MLE_App
                                         (mlhead, mlargs)) in
                                  FStar_All.pipe_left
                                    (maybe_eta_data_and_project_record g
                                       is_data t) _0_567 in
                                let l_app =
                                  FStar_List.fold_right
                                    (fun uu____3732  ->
                                       fun out  ->
                                         match uu____3732 with
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
                                                     }]) out)) lbs app in
                                (l_app, f, t))
                       | ((arg,uu____3745)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                          (formal_t,f',t)) when is_type g arg ->
                           let uu____3763 =
                             type_leq g formal_t
                               FStar_Extraction_ML_Syntax.ml_unit_ty in
                           if uu____3763
                           then
                             let _0_569 =
                               let _0_568 =
                                 FStar_Extraction_ML_Util.join
                                   arg.FStar_Syntax_Syntax.pos f f' in
                               (_0_568, t) in
                             extract_app is_data
                               (mlhead,
                                 ((FStar_Extraction_ML_Syntax.ml_unit,
                                    FStar_Extraction_ML_Syntax.E_PURE) ::
                                 mlargs_f)) _0_569 rest
                           else
                             failwith
                               (let _0_573 =
                                  FStar_Extraction_ML_Code.string_of_mlexpr
                                    g.FStar_Extraction_ML_UEnv.currentModule
                                    mlhead in
                                let _0_572 =
                                  FStar_Syntax_Print.term_to_string arg in
                                let _0_571 =
                                  FStar_Syntax_Print.tag_of_term arg in
                                let _0_570 =
                                  FStar_Extraction_ML_Code.string_of_mlty
                                    g.FStar_Extraction_ML_UEnv.currentModule
                                    formal_t in
                                FStar_Util.format4
                                  "Impossible: ill-typed application:\n\thead=%s, arg=%s, tag=%s\n\texpected type unit, got %s"
                                  _0_573 _0_572 _0_571 _0_570)
                       | ((e0,uu____3777)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                          (tExpected,f',t)) ->
                           let r = e0.FStar_Syntax_Syntax.pos in
                           let uu____3796 = term_as_mlexpr g e0 in
                           (match uu____3796 with
                            | (e0,f0,tInferred) ->
                                let e0 =
                                  maybe_coerce g e0 tInferred tExpected in
                                let _0_575 =
                                  let _0_574 =
                                    FStar_Extraction_ML_Util.join_l r
                                      [f; f'; f0] in
                                  (_0_574, t) in
                                extract_app is_data
                                  (mlhead, ((e0, f0) :: mlargs_f)) _0_575
                                  rest)
                       | uu____3812 ->
                           let uu____3819 =
                             FStar_Extraction_ML_Util.udelta_unfold g t in
                           (match uu____3819 with
                            | Some t ->
                                extract_app is_data (mlhead, mlargs_f) 
                                  (f, t) restArgs
                            | None  ->
                                err_ill_typed_application g top restArgs t)) in
                let extract_app_maybe_projector is_data mlhead uu____3855
                  args =
                  match uu____3855 with
                  | (f,t) ->
                      (match is_data with
                       | Some (FStar_Syntax_Syntax.Record_projector
                           uu____3874) ->
                           let rec remove_implicits args f t =
                             match (args, t) with
                             | ((a0,Some (FStar_Syntax_Syntax.Implicit
                                 uu____3924))::args,FStar_Extraction_ML_Syntax.MLTY_Fun
                                (uu____3926,f',t)) ->
                                 let _0_576 =
                                   FStar_Extraction_ML_Util.join
                                     a0.FStar_Syntax_Syntax.pos f f' in
                                 remove_implicits args _0_576 t
                             | uu____3951 -> (args, f, t) in
                           let uu____3966 = remove_implicits args f t in
                           (match uu____3966 with
                            | (args,f,t) ->
                                extract_app is_data (mlhead, []) (f, t) args)
                       | uu____3999 ->
                           extract_app is_data (mlhead, []) (f, t) args) in
                let uu____4006 = is_type g t in
                if uu____4006
                then
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
                else
                  (let head = FStar_Syntax_Util.un_uinst head in
                   match head.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_name _
                     |FStar_Syntax_Syntax.Tm_fvar _ ->
                       let uu____4017 =
                         let uu____4024 =
                           FStar_Extraction_ML_UEnv.lookup_term g head in
                         match uu____4024 with
                         | (FStar_Util.Inr u,q) -> (u, q)
                         | uu____4057 -> failwith "FIXME Ty" in
                       (match uu____4017 with
                        | ((head_ml,(vars,t),inst_ok),qual) ->
                            let has_typ_apps =
                              match args with
                              | (a,uu____4086)::uu____4087 -> is_type g a
                              | uu____4101 -> false in
                            let uu____4107 =
                              match vars with
                              | uu____4124::uu____4125 when
                                  (Prims.op_Negation has_typ_apps) && inst_ok
                                  -> (head_ml, t, args)
                              | uu____4132 ->
                                  let n = FStar_List.length vars in
                                  if n <= (FStar_List.length args)
                                  then
                                    let uu____4152 =
                                      FStar_Util.first_N n args in
                                    (match uu____4152 with
                                     | (prefix,rest) ->
                                         let prefixAsMLTypes =
                                           FStar_List.map
                                             (fun uu____4205  ->
                                                match uu____4205 with
                                                | (x,uu____4209) ->
                                                    term_as_mlty g x) prefix in
                                         let t =
                                           instantiate (vars, t)
                                             prefixAsMLTypes in
                                         let head =
                                           match head_ml.FStar_Extraction_ML_Syntax.expr
                                           with
                                           | FStar_Extraction_ML_Syntax.MLE_Name
                                             _
                                             |FStar_Extraction_ML_Syntax.MLE_Var
                                             _ ->
                                               let uu___142_4214 = head_ml in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (uu___142_4214.FStar_Extraction_ML_Syntax.expr);
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   = t;
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___142_4214.FStar_Extraction_ML_Syntax.loc)
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
                                                    ((let uu___143_4220 =
                                                        head in
                                                      {
                                                        FStar_Extraction_ML_Syntax.expr
                                                          =
                                                          (uu___143_4220.FStar_Extraction_ML_Syntax.expr);
                                                        FStar_Extraction_ML_Syntax.mlty
                                                          =
                                                          (FStar_Extraction_ML_Syntax.MLTY_Fun
                                                             (FStar_Extraction_ML_Syntax.ml_unit_ty,
                                                               FStar_Extraction_ML_Syntax.E_PURE,
                                                               t));
                                                        FStar_Extraction_ML_Syntax.loc
                                                          =
                                                          (uu___143_4220.FStar_Extraction_ML_Syntax.loc)
                                                      }),
                                                      [FStar_Extraction_ML_Syntax.ml_unit]))
                                                 (FStar_Extraction_ML_Syntax.with_ty
                                                    t)
                                           | uu____4221 ->
                                               failwith
                                                 "Impossible: Unexpected head term" in
                                         (head, t, rest))
                                  else err_uninst g head (vars, t) top in
                            (match uu____4107 with
                             | (head_ml,head_t,args) ->
                                 (match args with
                                  | [] ->
                                      let _0_577 =
                                        maybe_eta_data_and_project_record g
                                          qual head_t head_ml in
                                      (_0_577,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        head_t)
                                  | uu____4259 ->
                                      extract_app_maybe_projector qual
                                        head_ml
                                        (FStar_Extraction_ML_Syntax.E_PURE,
                                          head_t) args)))
                   | uu____4265 ->
                       let uu____4266 = term_as_mlexpr g head in
                       (match uu____4266 with
                        | (head,f,t) ->
                            extract_app_maybe_projector None head (f, t) args)))
       | FStar_Syntax_Syntax.Tm_ascribed (e0,tc,f) ->
           let t =
             match tc with
             | FStar_Util.Inl t -> term_as_mlty g t
             | FStar_Util.Inr c ->
                 term_as_mlty g (FStar_Syntax_Util.comp_result c) in
           let f =
             match f with
             | None  -> failwith "Ascription node with an empty effect label"
             | Some l -> effect_as_etag g l in
           let uu____4314 = check_term_as_mlexpr g e0 f t in
           (match uu____4314 with | (e,t) -> (e, f, t))
       | FStar_Syntax_Syntax.Tm_let ((is_rec,lbs),e') ->
           let top_level = FStar_Syntax_Syntax.is_top_level lbs in
           let uu____4335 =
             if is_rec
             then FStar_Syntax_Subst.open_let_rec lbs e'
             else
               (let uu____4343 = FStar_Syntax_Syntax.is_top_level lbs in
                if uu____4343
                then (lbs, e')
                else
                  (let lb = FStar_List.hd lbs in
                   let x =
                     FStar_Syntax_Syntax.freshen_bv
                       (FStar_Util.left lb.FStar_Syntax_Syntax.lbname) in
                   let lb =
                     let uu___144_4354 = lb in
                     {
                       FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                       FStar_Syntax_Syntax.lbunivs =
                         (uu___144_4354.FStar_Syntax_Syntax.lbunivs);
                       FStar_Syntax_Syntax.lbtyp =
                         (uu___144_4354.FStar_Syntax_Syntax.lbtyp);
                       FStar_Syntax_Syntax.lbeff =
                         (uu___144_4354.FStar_Syntax_Syntax.lbeff);
                       FStar_Syntax_Syntax.lbdef =
                         (uu___144_4354.FStar_Syntax_Syntax.lbdef)
                     } in
                   let e' =
                     FStar_Syntax_Subst.subst
                       [FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x)] e' in
                   ([lb], e'))) in
           (match uu____4335 with
            | (lbs,e') ->
                let lbs =
                  if top_level
                  then
                    FStar_All.pipe_right lbs
                      (FStar_List.map
                         (fun lb  ->
                            let tcenv =
                              let _0_578 =
                                FStar_Ident.lid_of_path
                                  (FStar_List.append
                                     (Prims.fst
                                        g.FStar_Extraction_ML_UEnv.currentModule)
                                     [Prims.snd
                                        g.FStar_Extraction_ML_UEnv.currentModule])
                                  FStar_Range.dummyRange in
                              FStar_TypeChecker_Env.set_current_module
                                g.FStar_Extraction_ML_UEnv.tcenv _0_578 in
                            FStar_Extraction_ML_UEnv.debug g
                              (fun uu____4374  ->
                                 FStar_Options.set_option "debug_level"
                                   (FStar_Options.List
                                      [FStar_Options.String "Norm";
                                      FStar_Options.String "Extraction"]));
                            (let lbdef =
                               let uu____4378 = FStar_Options.ml_ish () in
                               if uu____4378
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
                                   lb.FStar_Syntax_Syntax.lbdef in
                             let uu___145_4382 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___145_4382.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___145_4382.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___145_4382.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___145_4382.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef
                             })))
                  else lbs in
                let maybe_generalize uu____4396 =
                  match uu____4396 with
                  | { FStar_Syntax_Syntax.lbname = lbname_;
                      FStar_Syntax_Syntax.lbunivs = uu____4407;
                      FStar_Syntax_Syntax.lbtyp = t;
                      FStar_Syntax_Syntax.lbeff = lbeff;
                      FStar_Syntax_Syntax.lbdef = e;_} ->
                      let f_e = effect_as_etag g lbeff in
                      let t = FStar_Syntax_Subst.compress t in
                      (match t.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                           let _0_579 = FStar_List.hd bs in
                           FStar_All.pipe_right _0_579 (is_type_binder g) ->
                           let uu____4454 = FStar_Syntax_Subst.open_comp bs c in
                           (match uu____4454 with
                            | (bs,c) ->
                                let uu____4468 =
                                  let uu____4473 =
                                    FStar_Util.prefix_until
                                      (fun x  ->
                                         Prims.op_Negation
                                           (is_type_binder g x)) bs in
                                  match uu____4473 with
                                  | None  ->
                                      (bs, (FStar_Syntax_Util.comp_result c))
                                  | Some (bs,b,rest) ->
                                      let _0_580 =
                                        FStar_Syntax_Util.arrow (b :: rest) c in
                                      (bs, _0_580) in
                                (match uu____4468 with
                                 | (tbinders,tbody) ->
                                     let n_tbinders =
                                       FStar_List.length tbinders in
                                     let e =
                                       let _0_581 = normalize_abs e in
                                       FStar_All.pipe_right _0_581
                                         FStar_Syntax_Util.unmeta in
                                     (match e.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Tm_abs
                                          (bs,body,uu____4576) ->
                                          let uu____4599 =
                                            FStar_Syntax_Subst.open_term bs
                                              body in
                                          (match uu____4599 with
                                           | (bs,body) ->
                                               if
                                                 n_tbinders <=
                                                   (FStar_List.length bs)
                                               then
                                                 let uu____4629 =
                                                   FStar_Util.first_N
                                                     n_tbinders bs in
                                                 (match uu____4629 with
                                                  | (targs,rest_args) ->
                                                      let expected_source_ty
                                                        =
                                                        let s =
                                                          FStar_List.map2
                                                            (fun uu____4672 
                                                               ->
                                                               fun uu____4673
                                                                  ->
                                                                 match 
                                                                   (uu____4672,
                                                                    uu____4673)
                                                                 with
                                                                 | ((x,uu____4683),
                                                                    (y,uu____4685))
                                                                    ->
                                                                    FStar_Syntax_Syntax.NT
                                                                    (let _0_582
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    y in
                                                                    (x,
                                                                    _0_582)))
                                                            tbinders targs in
                                                        FStar_Syntax_Subst.subst
                                                          s tbody in
                                                      let env =
                                                        FStar_List.fold_left
                                                          (fun env  ->
                                                             fun uu____4694 
                                                               ->
                                                               match uu____4694
                                                               with
                                                               | (a,uu____4698)
                                                                   ->
                                                                   FStar_Extraction_ML_UEnv.extend_ty
                                                                    env a
                                                                    None) g
                                                          targs in
                                                      let expected_t =
                                                        term_as_mlty env
                                                          expected_source_ty in
                                                      let polytype =
                                                        let _0_583 =
                                                          FStar_All.pipe_right
                                                            targs
                                                            (FStar_List.map
                                                               (fun
                                                                  uu____4719 
                                                                  ->
                                                                  match uu____4719
                                                                  with
                                                                  | (x,uu____4725)
                                                                    ->
                                                                    FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                                    x)) in
                                                        (_0_583, expected_t) in
                                                      let add_unit =
                                                        match rest_args with
                                                        | [] ->
                                                            Prims.op_Negation
                                                              (is_fstar_value
                                                                 body)
                                                        | uu____4729 -> false in
                                                      let rest_args =
                                                        if add_unit
                                                        then unit_binder ::
                                                          rest_args
                                                        else rest_args in
                                                      let body =
                                                        match rest_args with
                                                        | [] -> body
                                                        | uu____4738 ->
                                                            FStar_Syntax_Util.abs
                                                              rest_args body
                                                              None in
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
                                                 fun uu____4794  ->
                                                   match uu____4794 with
                                                   | (a,uu____4798) ->
                                                       FStar_Extraction_ML_UEnv.extend_ty
                                                         env a None) g
                                              tbinders in
                                          let expected_t =
                                            term_as_mlty env tbody in
                                          let polytype =
                                            let _0_584 =
                                              FStar_All.pipe_right tbinders
                                                (FStar_List.map
                                                   (fun uu____4816  ->
                                                      match uu____4816 with
                                                      | (x,uu____4822) ->
                                                          FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                            x)) in
                                            (_0_584, expected_t) in
                                          let args =
                                            FStar_All.pipe_right tbinders
                                              (FStar_List.map
                                                 (fun uu____4828  ->
                                                    match uu____4828 with
                                                    | (bv,uu____4832) ->
                                                        let _0_585 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            bv in
                                                        FStar_All.pipe_right
                                                          _0_585
                                                          FStar_Syntax_Syntax.as_arg)) in
                                          let e =
                                            (FStar_Syntax_Syntax.mk
                                               (FStar_Syntax_Syntax.Tm_app
                                                  (e, args))) None
                                              e.FStar_Syntax_Syntax.pos in
                                          (lbname_, f_e,
                                            (t, (tbinders, polytype)), false,
                                            e)
                                      | uu____4870 -> err_value_restriction e)))
                       | uu____4880 ->
                           let expected_t = term_as_mlty g t in
                           (lbname_, f_e, (t, ([], ([], expected_t))), false,
                             e)) in
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
                                     None) env targs in
                      let expected_t =
                        if add_unit
                        then
                          FStar_Extraction_ML_Syntax.MLTY_Fun
                            (FStar_Extraction_ML_Syntax.ml_unit_ty,
                              FStar_Extraction_ML_Syntax.E_PURE,
                              (Prims.snd polytype))
                        else Prims.snd polytype in
                      let uu____5015 =
                        check_term_as_mlexpr env e f expected_t in
                      (match uu____5015 with
                       | (e,uu____5021) ->
                           let f = maybe_downgrade_eff env f expected_t in
                           (f,
                             {
                               FStar_Extraction_ML_Syntax.mllb_name = nm;
                               FStar_Extraction_ML_Syntax.mllb_tysc =
                                 (Some polytype);
                               FStar_Extraction_ML_Syntax.mllb_add_unit =
                                 add_unit;
                               FStar_Extraction_ML_Syntax.mllb_def = e;
                               FStar_Extraction_ML_Syntax.print_typ = true
                             })) in
                let lbs =
                  FStar_All.pipe_right lbs (FStar_List.map maybe_generalize) in
                let uu____5056 =
                  FStar_List.fold_right
                    (fun lb  ->
                       fun uu____5095  ->
                         match uu____5095 with
                         | (env,lbs) ->
                             let uu____5159 = lb in
                             (match uu____5159 with
                              | (lbname,uu____5184,(t,(uu____5186,polytype)),add_unit,uu____5189)
                                  ->
                                  let uu____5196 =
                                    FStar_Extraction_ML_UEnv.extend_lb env
                                      lbname t polytype add_unit true in
                                  (match uu____5196 with
                                   | (env,nm) -> (env, ((nm, lb) :: lbs)))))
                    lbs (g, []) in
                (match uu____5056 with
                 | (env_body,lbs) ->
                     let env_def = if is_rec then env_body else g in
                     let lbs =
                       FStar_All.pipe_right lbs
                         (FStar_List.map (check_lb env_def)) in
                     let e'_rng = e'.FStar_Syntax_Syntax.pos in
                     let uu____5339 = term_as_mlexpr env_body e' in
                     (match uu____5339 with
                      | (e',f',t') ->
                          let f =
                            let _0_587 =
                              let _0_586 = FStar_List.map Prims.fst lbs in f'
                                :: _0_586 in
                            FStar_Extraction_ML_Util.join_l e'_rng _0_587 in
                          let is_rec =
                            if is_rec = true
                            then FStar_Extraction_ML_Syntax.Rec
                            else FStar_Extraction_ML_Syntax.NonRec in
                          let _0_592 =
                            let _0_591 =
                              let _0_589 =
                                let _0_588 = FStar_List.map Prims.snd lbs in
                                (is_rec, [], _0_588) in
                              mk_MLE_Let top_level _0_589 e' in
                            let _0_590 =
                              FStar_Extraction_ML_Util.mlloc_of_range
                                t.FStar_Syntax_Syntax.pos in
                            FStar_Extraction_ML_Syntax.with_ty_loc t' _0_591
                              _0_590 in
                          (_0_592, f, t'))))
       | FStar_Syntax_Syntax.Tm_match (scrutinee,pats) ->
           let uu____5386 = term_as_mlexpr g scrutinee in
           (match uu____5386 with
            | (e,f_e,t_e) ->
                let uu____5396 = check_pats_for_ite pats in
                (match uu____5396 with
                 | (b,then_e,else_e) ->
                     let no_lift x t = x in
                     if b
                     then
                       (match (then_e, else_e) with
                        | (Some then_e,Some else_e) ->
                            let uu____5431 = term_as_mlexpr g then_e in
                            (match uu____5431 with
                             | (then_mle,f_then,t_then) ->
                                 let uu____5441 = term_as_mlexpr g else_e in
                                 (match uu____5441 with
                                  | (else_mle,f_else,t_else) ->
                                      let uu____5451 =
                                        let uu____5458 =
                                          type_leq g t_then t_else in
                                        if uu____5458
                                        then (t_else, no_lift)
                                        else
                                          (let uu____5470 =
                                             type_leq g t_else t_then in
                                           if uu____5470
                                           then (t_then, no_lift)
                                           else
                                             (FStar_Extraction_ML_Syntax.MLTY_Top,
                                               FStar_Extraction_ML_Syntax.apply_obj_repr)) in
                                      (match uu____5451 with
                                       | (t_branch,maybe_lift) ->
                                           let _0_597 =
                                             let _0_595 =
                                               FStar_Extraction_ML_Syntax.MLE_If
                                                 (let _0_594 =
                                                    maybe_lift then_mle
                                                      t_then in
                                                  let _0_593 =
                                                    Some
                                                      (maybe_lift else_mle
                                                         t_else) in
                                                  (e, _0_594, _0_593)) in
                                             FStar_All.pipe_left
                                               (FStar_Extraction_ML_Syntax.with_ty
                                                  t_branch) _0_595 in
                                           let _0_596 =
                                             FStar_Extraction_ML_Util.join
                                               then_e.FStar_Syntax_Syntax.pos
                                               f_then f_else in
                                           (_0_597, _0_596, t_branch))))
                        | uu____5500 ->
                            failwith
                              "ITE pats matched but then and else expressions not found?")
                     else
                       (let uu____5509 =
                          FStar_All.pipe_right pats
                            (FStar_Util.fold_map
                               (fun compat  ->
                                  fun br  ->
                                    let uu____5559 =
                                      FStar_Syntax_Subst.open_branch br in
                                    match uu____5559 with
                                    | (pat,when_opt,branch) ->
                                        let uu____5589 =
                                          extract_pat g pat t_e in
                                        (match uu____5589 with
                                         | (env,p,pat_t_compat) ->
                                             let uu____5620 =
                                               match when_opt with
                                               | None  ->
                                                   (None,
                                                     FStar_Extraction_ML_Syntax.E_PURE)
                                               | Some w ->
                                                   let uu____5635 =
                                                     term_as_mlexpr env w in
                                                   (match uu____5635 with
                                                    | (w,f_w,t_w) ->
                                                        let w =
                                                          maybe_coerce env w
                                                            t_w
                                                            FStar_Extraction_ML_Syntax.ml_bool_ty in
                                                        ((Some w), f_w)) in
                                             (match uu____5620 with
                                              | (when_opt,f_when) ->
                                                  let uu____5663 =
                                                    term_as_mlexpr env branch in
                                                  (match uu____5663 with
                                                   | (mlbranch,f_branch,t_branch)
                                                       ->
                                                       let _0_598 =
                                                         FStar_All.pipe_right
                                                           p
                                                           (FStar_List.map
                                                              (fun uu____5718
                                                                  ->
                                                                 match uu____5718
                                                                 with
                                                                 | (p,wopt)
                                                                    ->
                                                                    let when_clause
                                                                    =
                                                                    FStar_Extraction_ML_Util.conjoin_opt
                                                                    wopt
                                                                    when_opt in
                                                                    (p,
                                                                    (when_clause,
                                                                    f_when),
                                                                    (mlbranch,
                                                                    f_branch,
                                                                    t_branch)))) in
                                                       ((compat &&
                                                           pat_t_compat),
                                                         _0_598))))) true) in
                        match uu____5509 with
                        | (pat_t_compat,mlbranches) ->
                            let mlbranches = FStar_List.flatten mlbranches in
                            let e =
                              if pat_t_compat
                              then e
                              else
                                (FStar_Extraction_ML_UEnv.debug g
                                   (fun uu____5794  ->
                                      let _0_600 =
                                        FStar_Extraction_ML_Code.string_of_mlexpr
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          e in
                                      let _0_599 =
                                        FStar_Extraction_ML_Code.string_of_mlty
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          t_e in
                                      FStar_Util.print2
                                        "Coercing scrutinee %s from type %s because pattern type is incompatible\n"
                                        _0_600 _0_599);
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty t_e)
                                   (FStar_Extraction_ML_Syntax.MLE_Coerce
                                      (e, t_e,
                                        FStar_Extraction_ML_Syntax.MLTY_Top))) in
                            (match mlbranches with
                             | [] ->
                                 let uu____5807 =
                                   let _0_602 =
                                     let _0_601 =
                                       FStar_Syntax_Syntax.lid_as_fv
                                         FStar_Syntax_Const.failwith_lid
                                         FStar_Syntax_Syntax.Delta_constant
                                         None in
                                     FStar_Extraction_ML_UEnv.lookup_fv g
                                       _0_601 in
                                   FStar_All.pipe_left FStar_Util.right
                                     _0_602 in
                                 (match uu____5807 with
                                  | (fw,uu____5830,uu____5831) ->
                                      let _0_606 =
                                        let _0_605 =
                                          FStar_Extraction_ML_Syntax.MLE_App
                                            (let _0_604 =
                                               let _0_603 =
                                                 FStar_All.pipe_left
                                                   (FStar_Extraction_ML_Syntax.with_ty
                                                      FStar_Extraction_ML_Syntax.ml_string_ty)
                                                   (FStar_Extraction_ML_Syntax.MLE_Const
                                                      (FStar_Extraction_ML_Syntax.MLC_String
                                                         "unreachable")) in
                                               [_0_603] in
                                             (fw, _0_604)) in
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             FStar_Extraction_ML_Syntax.ml_unit_ty)
                                          _0_605 in
                                      (_0_606,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        FStar_Extraction_ML_Syntax.ml_unit_ty))
                             | (uu____5833,uu____5834,(uu____5835,f_first,t_first))::rest
                                 ->
                                 let uu____5867 =
                                   FStar_List.fold_left
                                     (fun uu____5883  ->
                                        fun uu____5884  ->
                                          match (uu____5883, uu____5884) with
                                          | ((topt,f),(uu____5914,uu____5915,
                                                       (uu____5916,f_branch,t_branch)))
                                              ->
                                              let f =
                                                FStar_Extraction_ML_Util.join
                                                  top.FStar_Syntax_Syntax.pos
                                                  f f_branch in
                                              let topt =
                                                match topt with
                                                | None  -> None
                                                | Some t ->
                                                    let uu____5947 =
                                                      type_leq g t t_branch in
                                                    if uu____5947
                                                    then Some t_branch
                                                    else
                                                      (let uu____5950 =
                                                         type_leq g t_branch
                                                           t in
                                                       if uu____5950
                                                       then Some t
                                                       else None) in
                                              (topt, f))
                                     ((Some t_first), f_first) rest in
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
                                                      | Some uu____6025 -> b in
                                                    (p, wopt, b))) in
                                      let t_match =
                                        match topt with
                                        | None  ->
                                            FStar_Extraction_ML_Syntax.MLTY_Top
                                        | Some t -> t in
                                      let _0_607 =
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             t_match)
                                          (FStar_Extraction_ML_Syntax.MLE_Match
                                             (e, mlbranches)) in
                                      (_0_607, f_match, t_match)))))))
let fresh: Prims.string -> (Prims.string* Prims.int) =
  let c = FStar_Util.mk_ref (Prims.parse_int "0") in
  fun x  -> FStar_Util.incr c; (let _0_608 = FStar_ST.read c in (x, _0_608))
let ind_discriminator_body:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlmodule1
  =
  fun env  ->
    fun discName  ->
      fun constrName  ->
        let uu____6057 =
          FStar_TypeChecker_Env.lookup_lid env.FStar_Extraction_ML_UEnv.tcenv
            discName in
        match uu____6057 with
        | (uu____6060,fstar_disc_type) ->
            let wildcards =
              let uu____6068 =
                (FStar_Syntax_Subst.compress fstar_disc_type).FStar_Syntax_Syntax.n in
              match uu____6068 with
              | FStar_Syntax_Syntax.Tm_arrow (binders,uu____6075) ->
                  let _0_610 =
                    FStar_All.pipe_right binders
                      (FStar_List.filter
                         (fun uu___139_6105  ->
                            match uu___139_6105 with
                            | (uu____6109,Some (FStar_Syntax_Syntax.Implicit
                               uu____6110)) -> true
                            | uu____6112 -> false)) in
                  FStar_All.pipe_right _0_610
                    (FStar_List.map
                       (fun uu____6123  ->
                          let _0_609 = fresh "_" in
                          (_0_609, FStar_Extraction_ML_Syntax.MLTY_Top)))
              | uu____6129 -> failwith "Discriminator must be a function" in
            let mlid = fresh "_discr_" in
            let targ = FStar_Extraction_ML_Syntax.MLTY_Top in
            let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top in
            let discrBody =
              let _0_624 =
                FStar_Extraction_ML_Syntax.MLE_Fun
                  (let _0_623 =
                     let _0_622 =
                       FStar_Extraction_ML_Syntax.MLE_Match
                         (let _0_621 =
                            let _0_612 =
                              FStar_Extraction_ML_Syntax.MLE_Name
                                (let _0_611 =
                                   FStar_Extraction_ML_Syntax.idsym mlid in
                                 ([], _0_611)) in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty targ)
                              _0_612 in
                          let _0_620 =
                            let _0_619 =
                              let _0_615 =
                                FStar_Extraction_ML_Syntax.MLP_CTor
                                  (let _0_613 =
                                     FStar_Extraction_ML_Syntax.mlpath_of_lident
                                       constrName in
                                   (_0_613,
                                     [FStar_Extraction_ML_Syntax.MLP_Wild])) in
                              let _0_614 =
                                FStar_All.pipe_left
                                  (FStar_Extraction_ML_Syntax.with_ty
                                     FStar_Extraction_ML_Syntax.ml_bool_ty)
                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                     (FStar_Extraction_ML_Syntax.MLC_Bool
                                        true)) in
                              (_0_615, None, _0_614) in
                            let _0_618 =
                              let _0_617 =
                                let _0_616 =
                                  FStar_All.pipe_left
                                    (FStar_Extraction_ML_Syntax.with_ty
                                       FStar_Extraction_ML_Syntax.ml_bool_ty)
                                    (FStar_Extraction_ML_Syntax.MLE_Const
                                       (FStar_Extraction_ML_Syntax.MLC_Bool
                                          false)) in
                                (FStar_Extraction_ML_Syntax.MLP_Wild, None,
                                  _0_616) in
                              [_0_617] in
                            _0_619 :: _0_618 in
                          (_0_621, _0_620)) in
                     FStar_All.pipe_left
                       (FStar_Extraction_ML_Syntax.with_ty
                          FStar_Extraction_ML_Syntax.ml_bool_ty) _0_622 in
                   ((FStar_List.append wildcards [(mlid, targ)]), _0_623)) in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty disc_ty) _0_624 in
            FStar_Extraction_ML_Syntax.MLM_Let
              (let _0_627 =
                 let _0_626 =
                   let _0_625 =
                     FStar_Extraction_ML_UEnv.convIdent
                       discName.FStar_Ident.ident in
                   {
                     FStar_Extraction_ML_Syntax.mllb_name = _0_625;
                     FStar_Extraction_ML_Syntax.mllb_tysc = None;
                     FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                     FStar_Extraction_ML_Syntax.mllb_def = discrBody;
                     FStar_Extraction_ML_Syntax.print_typ = false
                   } in
                 [_0_626] in
               (FStar_Extraction_ML_Syntax.NonRec, [], _0_627))