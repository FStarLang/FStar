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
  (let uu____78 =
     let uu____79 = FStar_Range.string_of_range r  in
     FStar_Util.format2 "%s: %s\n" uu____79 msg  in
   FStar_All.pipe_left FStar_Util.print_string uu____78);
  failwith msg 
let err_uninst env t uu____107 app =
  match uu____107 with
  | (vars,ty) ->
      let uu____122 =
        let uu____123 = FStar_Syntax_Print.term_to_string t  in
        let uu____124 =
          let uu____125 =
            FStar_All.pipe_right vars (FStar_List.map Prims.fst)  in
          FStar_All.pipe_right uu____125 (FStar_String.concat ", ")  in
        let uu____134 =
          FStar_Extraction_ML_Code.string_of_mlty
            env.FStar_Extraction_ML_UEnv.currentModule ty
           in
        let uu____135 = FStar_Syntax_Print.term_to_string app  in
        FStar_Util.format4
          "Variable %s has a polymorphic type (forall %s. %s); expected it to be fully instantiated, but got %s"
          uu____123 uu____124 uu____134 uu____135
         in
      fail t.FStar_Syntax_Syntax.pos uu____122
  
let err_ill_typed_application env t args ty =
  let uu____166 =
    let uu____167 = FStar_Syntax_Print.term_to_string t  in
    let uu____168 =
      let uu____169 =
        FStar_All.pipe_right args
          (FStar_List.map
             (fun uu____177  ->
                match uu____177 with
                | (x,uu____181) -> FStar_Syntax_Print.term_to_string x))
         in
      FStar_All.pipe_right uu____169 (FStar_String.concat " ")  in
    let uu____183 =
      FStar_Extraction_ML_Code.string_of_mlty
        env.FStar_Extraction_ML_UEnv.currentModule ty
       in
    FStar_Util.format3
      "Ill-typed application: application is %s \n remaining args are %s\nml type of head is %s\n"
      uu____167 uu____168 uu____183
     in
  fail t.FStar_Syntax_Syntax.pos uu____166 
let err_value_restriction t =
  let uu____195 =
    let uu____196 = FStar_Syntax_Print.tag_of_term t  in
    let uu____197 = FStar_Syntax_Print.term_to_string t  in
    FStar_Util.format2
      "Refusing to generalize because of the value restriction: (%s) %s"
      uu____196 uu____197
     in
  fail t.FStar_Syntax_Syntax.pos uu____195 
let err_unexpected_eff t f0 f1 =
  let uu____219 =
    let uu____220 = FStar_Syntax_Print.term_to_string t  in
    FStar_Util.format3 "for expression %s, Expected effect %s; got effect %s"
      uu____220 (FStar_Extraction_ML_Util.eff_to_string f0)
      (FStar_Extraction_ML_Util.eff_to_string f1)
     in
  fail t.FStar_Syntax_Syntax.pos uu____219 
let effect_as_etag :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Ident.lident -> FStar_Extraction_ML_Syntax.e_tag
  =
  let cache = FStar_Util.smap_create (Prims.parse_int "20")  in
  let rec delta_norm_eff g l =
    let uu____234 = FStar_Util.smap_try_find cache l.FStar_Ident.str  in
    match uu____234 with
    | Some l1 -> l1
    | None  ->
        let res =
          let uu____238 =
            FStar_TypeChecker_Env.lookup_effect_abbrev
              g.FStar_Extraction_ML_UEnv.tcenv [FStar_Syntax_Syntax.U_zero] l
             in
          match uu____238 with
          | None  -> l
          | Some (uu____244,c) ->
              delta_norm_eff g (FStar_Syntax_Util.comp_effect_name c)
           in
        (FStar_Util.smap_add cache l.FStar_Ident.str res; res)
     in
  fun g  ->
    fun l  ->
      let l1 = delta_norm_eff g l  in
      if FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_PURE_lid
      then FStar_Extraction_ML_Syntax.E_PURE
      else
        if FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_GHOST_lid
        then FStar_Extraction_ML_Syntax.E_GHOST
        else FStar_Extraction_ML_Syntax.E_IMPURE
  
let rec is_arity :
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t  in
      let uu____261 =
        let uu____262 = FStar_Syntax_Subst.compress t1  in
        uu____262.FStar_Syntax_Syntax.n  in
      match uu____261 with
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
          let uu____285 =
            FStar_TypeChecker_Env.result_typ
              env.FStar_Extraction_ML_UEnv.tcenv c
             in
          is_arity env uu____285
      | FStar_Syntax_Syntax.Tm_fvar uu____286 ->
          let t2 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Normalize.AllowUnboundUniverses;
              FStar_TypeChecker_Normalize.EraseUniverses;
              FStar_TypeChecker_Normalize.UnfoldUntil
                FStar_Syntax_Syntax.Delta_constant]
              env.FStar_Extraction_ML_UEnv.tcenv t1
             in
          let uu____288 =
            let uu____289 = FStar_Syntax_Subst.compress t2  in
            uu____289.FStar_Syntax_Syntax.n  in
          (match uu____288 with
           | FStar_Syntax_Syntax.Tm_fvar uu____292 -> false
           | uu____293 -> is_arity env t2)
      | FStar_Syntax_Syntax.Tm_app uu____294 ->
          let uu____304 = FStar_Syntax_Util.head_and_args t1  in
          (match uu____304 with | (head1,uu____315) -> is_arity env head1)
      | FStar_Syntax_Syntax.Tm_uinst (head1,uu____331) -> is_arity env head1
      | FStar_Syntax_Syntax.Tm_refine (x,uu____337) ->
          is_arity env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_abs (_,body,_)|FStar_Syntax_Syntax.Tm_let
        (_,body) -> is_arity env body
      | FStar_Syntax_Syntax.Tm_match (uu____366,branches) ->
          (match branches with
           | (uu____394,uu____395,e)::uu____397 -> is_arity env e
           | uu____433 -> false)
  
let rec is_type_aux :
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed _|FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____453 =
            let uu____454 = FStar_Syntax_Print.tag_of_term t1  in
            FStar_Util.format1 "Impossible: %s" uu____454  in
          failwith uu____453
      | FStar_Syntax_Syntax.Tm_constant uu____455 -> false
      | FStar_Syntax_Syntax.Tm_type _
        |FStar_Syntax_Syntax.Tm_refine _|FStar_Syntax_Syntax.Tm_arrow _ ->
          true
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.failwith_lid ->
          false
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____461 =
            FStar_TypeChecker_Env.is_type_constructor
              env.FStar_Extraction_ML_UEnv.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          if uu____461
          then true
          else
            (let uu____467 =
               FStar_TypeChecker_Env.lookup_lid
                 env.FStar_Extraction_ML_UEnv.tcenv
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             match uu____467 with | (uu____474,t2) -> is_arity env t2)
      | FStar_Syntax_Syntax.Tm_uvar (_,t2)
        |FStar_Syntax_Syntax.Tm_bvar
         { FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _;
           FStar_Syntax_Syntax.sort = t2;_}|FStar_Syntax_Syntax.Tm_name
         { FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _;
           FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____495,uu____496) ->
          is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____516) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_abs (uu____521,body,uu____523) ->
          is_type_aux env body
      | FStar_Syntax_Syntax.Tm_let (uu____546,body) -> is_type_aux env body
      | FStar_Syntax_Syntax.Tm_match (uu____558,branches) ->
          (match branches with
           | (uu____586,uu____587,e)::uu____589 -> is_type_aux env e
           | uu____625 -> failwith "Empty branches")
      | FStar_Syntax_Syntax.Tm_meta (t2,uu____638) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_app (head1,uu____644) -> is_type_aux env head1
  
let is_type :
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let b = is_type_aux env t  in
      FStar_Extraction_ML_UEnv.debug env
        (fun uu____667  ->
           if b
           then
             let uu____668 = FStar_Syntax_Print.term_to_string t  in
             let uu____669 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.print2 "is_type %s (%s)\n" uu____668 uu____669
           else
             (let uu____671 = FStar_Syntax_Print.term_to_string t  in
              let uu____672 = FStar_Syntax_Print.tag_of_term t  in
              FStar_Util.print2 "not a type %s (%s)\n" uu____671 uu____672));
      b
  
let is_type_binder env x =
  is_arity env (Prims.fst x).FStar_Syntax_Syntax.sort 
let is_constructor : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____692 =
      let uu____693 = FStar_Syntax_Subst.compress t  in
      uu____693.FStar_Syntax_Syntax.n  in
    match uu____692 with
    | FStar_Syntax_Syntax.Tm_fvar
      { FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _;
        FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor );_}
      |FStar_Syntax_Syntax.Tm_fvar
      { FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _;
        FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor
          _);_}
        -> true
    | uu____701 -> false
  
let rec is_fstar_value : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____705 =
      let uu____706 = FStar_Syntax_Subst.compress t  in
      uu____706.FStar_Syntax_Syntax.n  in
    match uu____705 with
    | FStar_Syntax_Syntax.Tm_constant _
      |FStar_Syntax_Syntax.Tm_bvar _
       |FStar_Syntax_Syntax.Tm_fvar _|FStar_Syntax_Syntax.Tm_abs _ -> true
    | FStar_Syntax_Syntax.Tm_app (head1,args) ->
        let uu____729 = is_constructor head1  in
        if uu____729
        then
          FStar_All.pipe_right args
            (FStar_List.for_all
               (fun uu____737  ->
                  match uu____737 with | (te,uu____741) -> is_fstar_value te))
        else false
    | FStar_Syntax_Syntax.Tm_meta (t1,_)|FStar_Syntax_Syntax.Tm_ascribed
      (t1,_,_) -> is_fstar_value t1
    | uu____762 -> false
  
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
    | FStar_Extraction_ML_Syntax.MLE_Record (uu____775,fields) ->
        FStar_Util.for_all
          (fun uu____787  ->
             match uu____787 with | (uu____790,e1) -> is_ml_value e1) fields
    | uu____792 -> false
  
let normalize_abs : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t0  ->
    let rec aux bs t copt =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_abs (bs',body,copt1) ->
          aux (FStar_List.append bs bs') body copt1
      | uu____852 ->
          let e' = FStar_Syntax_Util.unascribe t1  in
          let uu____854 = FStar_Syntax_Util.is_fun e'  in
          if uu____854
          then aux bs e' copt
          else FStar_Syntax_Util.abs bs e' copt
       in
    aux [] t0 None
  
let unit_binder : FStar_Syntax_Syntax.binder =
  let uu____863 =
    FStar_Syntax_Syntax.new_bv None FStar_TypeChecker_Common.t_unit  in
  FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____863 
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
      (let uu____907 = FStar_List.hd l  in
       match uu____907 with
       | (p1,w1,e1) ->
           let uu____926 =
             let uu____931 = FStar_List.tl l  in FStar_List.hd uu____931  in
           (match uu____926 with
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
                 | uu____970 -> def)))
  
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
          let e1 =
            let uu____1013 = erasable g f ty  in
            if uu____1013
            then
              let uu____1014 =
                type_leq g ty FStar_Extraction_ML_Syntax.ml_unit_ty  in
              (if uu____1014
               then FStar_Extraction_ML_Syntax.ml_unit
               else
                 FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty)
                   (FStar_Extraction_ML_Syntax.MLE_Coerce
                      (FStar_Extraction_ML_Syntax.ml_unit,
                        FStar_Extraction_ML_Syntax.ml_unit_ty, ty)))
            else e  in
          (e1, f, ty)
  
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
          let ty1 = eraseTypeDeep g ty  in
          let uu____1030 = (type_leq_c g (Some e) ty1) expect  in
          match uu____1030 with
          | (true ,Some e') -> e'
          | uu____1036 ->
              (FStar_Extraction_ML_UEnv.debug g
                 (fun uu____1041  ->
                    let uu____1042 =
                      FStar_Extraction_ML_Code.string_of_mlexpr
                        g.FStar_Extraction_ML_UEnv.currentModule e
                       in
                    let uu____1043 =
                      FStar_Extraction_ML_Code.string_of_mlty
                        g.FStar_Extraction_ML_UEnv.currentModule ty1
                       in
                    let uu____1044 =
                      FStar_Extraction_ML_Code.string_of_mlty
                        g.FStar_Extraction_ML_UEnv.currentModule expect
                       in
                    FStar_Util.print3
                      "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n"
                      uu____1042 uu____1043 uu____1044);
               FStar_All.pipe_left
                 (FStar_Extraction_ML_Syntax.with_ty expect)
                 (FStar_Extraction_ML_Syntax.MLE_Coerce (e, ty1, expect)))
  
let bv_as_mlty :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlty
  =
  fun g  ->
    fun bv  ->
      let uu____1051 = FStar_Extraction_ML_UEnv.lookup_bv g bv  in
      match uu____1051 with
      | FStar_Util.Inl (uu____1052,t) -> t
      | uu____1059 -> FStar_Extraction_ML_Syntax.MLTY_Top
  
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
      let uu____1093 =
        (fun t1  ->
           match t1 with
           | FStar_Extraction_ML_Syntax.MLTY_Top  -> true
           | FStar_Extraction_ML_Syntax.MLTY_Named uu____1095 ->
               let uu____1099 = FStar_Extraction_ML_Util.udelta_unfold g t1
                  in
               (match uu____1099 with
                | None  -> false
                | Some t2 ->
                    (let rec is_top_ty t3 =
                       match t3 with
                       | FStar_Extraction_ML_Syntax.MLTY_Top  -> true
                       | FStar_Extraction_ML_Syntax.MLTY_Named uu____1106 ->
                           let uu____1110 =
                             FStar_Extraction_ML_Util.udelta_unfold g t3  in
                           (match uu____1110 with
                            | None  -> false
                            | Some t4 -> is_top_ty t4)
                       | uu____1113 -> false  in
                     is_top_ty) t2)
           | uu____1114 -> false) mlt
         in
      if uu____1093
      then
        let t1 =
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
        term_as_mlty' g t1
      else mlt

and term_as_mlty' :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlty
  =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_bvar _
        |FStar_Syntax_Syntax.Tm_delayed _|FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____1122 =
            let uu____1123 = FStar_Syntax_Print.term_to_string t1  in
            FStar_Util.format1 "Impossible: Unexpected term %s" uu____1123
             in
          failwith uu____1122
      | FStar_Syntax_Syntax.Tm_constant uu____1124 ->
          FStar_Extraction_ML_UEnv.unknownType
      | FStar_Syntax_Syntax.Tm_uvar uu____1125 ->
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
          let uu____1183 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____1183 with
           | (bs1,c1) ->
               let uu____1188 = binders_as_ml_binders env bs1  in
               (match uu____1188 with
                | (mlbs,env1) ->
                    let t_ret =
                      let eff =
                        FStar_TypeChecker_Env.norm_eff_name
                          env1.FStar_Extraction_ML_UEnv.tcenv
                          (FStar_Syntax_Util.comp_effect_name c1)
                         in
                      let ed =
                        FStar_TypeChecker_Env.get_effect_decl
                          env1.FStar_Extraction_ML_UEnv.tcenv eff
                         in
                      let uu____1205 =
                        FStar_All.pipe_right
                          ed.FStar_Syntax_Syntax.qualifiers
                          (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                         in
                      if uu____1205
                      then
                        let t2 =
                          let uu____1208 =
                            FStar_TypeChecker_Env.lcomp_of_comp
                              env1.FStar_Extraction_ML_UEnv.tcenv c1
                             in
                          FStar_TypeChecker_Util.reify_comp
                            env1.FStar_Extraction_ML_UEnv.tcenv uu____1208
                           in
                        let res = term_as_mlty' env1 t2  in res
                      else
                        (let uu____1211 =
                           FStar_TypeChecker_Env.result_typ
                             env1.FStar_Extraction_ML_UEnv.tcenv c1
                            in
                         term_as_mlty' env1 uu____1211)
                       in
                    let erase1 =
                      effect_as_etag env1
                        (FStar_Syntax_Util.comp_effect_name c1)
                       in
                    let uu____1213 =
                      FStar_List.fold_right
                        (fun uu____1220  ->
                           fun uu____1221  ->
                             match (uu____1220, uu____1221) with
                             | ((uu____1232,t2),(tag,t')) ->
                                 (FStar_Extraction_ML_Syntax.E_PURE,
                                   (FStar_Extraction_ML_Syntax.MLTY_Fun
                                      (t2, tag, t')))) mlbs (erase1, t_ret)
                       in
                    (match uu____1213 with | (uu____1240,t2) -> t2)))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let res =
            let uu____1259 =
              let uu____1260 = FStar_Syntax_Util.un_uinst head1  in
              uu____1260.FStar_Syntax_Syntax.n  in
            match uu____1259 with
            | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
            | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv args
            | FStar_Syntax_Syntax.Tm_app (head2,args') ->
                let uu____1281 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app
                       (head2, (FStar_List.append args' args))) None
                    t1.FStar_Syntax_Syntax.pos
                   in
                term_as_mlty' env uu____1281
            | uu____1297 -> FStar_Extraction_ML_UEnv.unknownType  in
          res
      | FStar_Syntax_Syntax.Tm_abs (bs,ty,uu____1300) ->
          let uu____1323 = FStar_Syntax_Subst.open_term bs ty  in
          (match uu____1323 with
           | (bs1,ty1) ->
               let uu____1328 = binders_as_ml_binders env bs1  in
               (match uu____1328 with | (bts,env1) -> term_as_mlty' env1 ty1))
      | FStar_Syntax_Syntax.Tm_type _
        |FStar_Syntax_Syntax.Tm_let _|FStar_Syntax_Syntax.Tm_match _ ->
          FStar_Extraction_ML_UEnv.unknownType

and arg_as_mlty :
  FStar_Extraction_ML_UEnv.env ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual) ->
      FStar_Extraction_ML_Syntax.mlty
  =
  fun g  ->
    fun uu____1346  ->
      match uu____1346 with
      | (a,uu____1350) ->
          let uu____1351 = is_type g a  in
          if uu____1351
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
        let uu____1356 =
          FStar_TypeChecker_Util.arrow_formals
            g.FStar_Extraction_ML_UEnv.tcenv
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.ty
           in
        match uu____1356 with
        | (formals,t) ->
            let mlargs = FStar_List.map (arg_as_mlty g) args  in
            let mlargs1 =
              let n_args = FStar_List.length args  in
              if (FStar_List.length formals) > n_args
              then
                let uu____1385 = FStar_Util.first_N n_args formals  in
                match uu____1385 with
                | (uu____1399,rest) ->
                    let uu____1413 =
                      FStar_List.map
                        (fun uu____1417  ->
                           FStar_Extraction_ML_UEnv.erasedContent) rest
                       in
                    FStar_List.append mlargs uu____1413
              else mlargs  in
            let nm =
              let uu____1422 =
                FStar_Extraction_ML_UEnv.maybe_mangle_type_projector g fv  in
              match uu____1422 with
              | Some p -> p
              | None  ->
                  FStar_Extraction_ML_Syntax.mlpath_of_lident
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            FStar_Extraction_ML_Syntax.MLTY_Named (mlargs1, nm)

and binders_as_ml_binders :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.binders ->
      ((FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)
        Prims.list * FStar_Extraction_ML_UEnv.env)
  =
  fun g  ->
    fun bs  ->
      let uu____1437 =
        FStar_All.pipe_right bs
          (FStar_List.fold_left
             (fun uu____1461  ->
                fun b  ->
                  match uu____1461 with
                  | (ml_bs,env) ->
                      let uu____1491 = is_type_binder g b  in
                      if uu____1491
                      then
                        let b1 = Prims.fst b  in
                        let env1 =
                          FStar_Extraction_ML_UEnv.extend_ty env b1
                            (Some FStar_Extraction_ML_Syntax.MLTY_Top)
                           in
                        let ml_b =
                          let uu____1506 =
                            FStar_Extraction_ML_UEnv.bv_as_ml_termvar b1  in
                          (uu____1506, FStar_Extraction_ML_Syntax.ml_unit_ty)
                           in
                        ((ml_b :: ml_bs), env1)
                      else
                        (let b1 = Prims.fst b  in
                         let t = term_as_mlty env b1.FStar_Syntax_Syntax.sort
                            in
                         let env1 =
                           FStar_Extraction_ML_UEnv.extend_bv env b1 
                             ([], t) false false false
                            in
                         let ml_b =
                           let uu____1530 =
                             FStar_Extraction_ML_UEnv.bv_as_ml_termvar b1  in
                           (uu____1530, t)  in
                         ((ml_b :: ml_bs), env1))) ([], g))
         in
      match uu____1437 with | (ml_bs,env) -> ((FStar_List.rev ml_bs), env)

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
      | (FStar_Extraction_ML_Syntax.MLE_Seq es1,uu____1590) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (FStar_List.append es1 [e2])
      | (uu____1592,FStar_Extraction_ML_Syntax.MLE_Seq es2) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (e1 :: es2)
      | uu____1595 -> FStar_Extraction_ML_Syntax.MLE_Seq [e1; e2]
  
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
                    | uu____1617 when
                        (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
                          =
                          FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr
                        -> body.FStar_Extraction_ML_Syntax.expr
                    | uu____1618 ->
                        mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def
                          body)
             | uu____1619 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body))
        | uu____1621 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body)
  
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
           | uu____1635 ->
               (match q with
                | Some (FStar_Syntax_Syntax.Record_ctor (ty,fns)) ->
                    let path =
                      FStar_List.map FStar_Ident.text_of_id ty.FStar_Ident.ns
                       in
                    let fs = record_fields fns pats  in
                    FStar_Extraction_ML_Syntax.MLP_Record (path, fs)
                | uu____1651 -> p))
      | uu____1653 -> p
  
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
                       (fun uu____1692  ->
                          let uu____1693 =
                            FStar_Extraction_ML_Code.string_of_mlty
                              g.FStar_Extraction_ML_UEnv.currentModule t'
                             in
                          let uu____1694 =
                            FStar_Extraction_ML_Code.string_of_mlty
                              g.FStar_Extraction_ML_UEnv.currentModule t
                             in
                          FStar_Util.print2
                            "Expected pattern type %s; got pattern type %s\n"
                            uu____1693 uu____1694)
                   else ();
                   ok)
               in
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_disj uu____1703 ->
                failwith "Impossible: Nested disjunctive pattern"
            | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int
                (c,None )) ->
                let i = FStar_Const.Const_int (c, None)  in
                let x = FStar_Extraction_ML_Syntax.gensym ()  in
                let when_clause =
                  let uu____1728 =
                    let uu____1729 =
                      let uu____1733 =
                        let uu____1735 =
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty
                               FStar_Extraction_ML_Syntax.ml_int_ty)
                            (FStar_Extraction_ML_Syntax.MLE_Var x)
                           in
                        let uu____1736 =
                          let uu____1738 =
                            let uu____1739 =
                              let uu____1740 =
                                FStar_Extraction_ML_Util.mlconst_of_const'
                                  p.FStar_Syntax_Syntax.p i
                                 in
                              FStar_All.pipe_left
                                (fun _0_30  ->
                                   FStar_Extraction_ML_Syntax.MLE_Const _0_30)
                                uu____1740
                               in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.ml_int_ty)
                              uu____1739
                             in
                          [uu____1738]  in
                        uu____1735 :: uu____1736  in
                      (FStar_Extraction_ML_Util.prims_op_equality,
                        uu____1733)
                       in
                    FStar_Extraction_ML_Syntax.MLE_App uu____1729  in
                  FStar_All.pipe_left
                    (FStar_Extraction_ML_Syntax.with_ty
                       FStar_Extraction_ML_Syntax.ml_bool_ty) uu____1728
                   in
                let uu____1742 = ok FStar_Extraction_ML_Syntax.ml_int_ty  in
                (g,
                  (Some
                     ((FStar_Extraction_ML_Syntax.MLP_Var x), [when_clause])),
                  uu____1742)
            | FStar_Syntax_Syntax.Pat_constant s ->
                let t =
                  FStar_TypeChecker_TcTerm.tc_constant FStar_Range.dummyRange
                    s
                   in
                let mlty = term_as_mlty g t  in
                let uu____1754 =
                  let uu____1759 =
                    let uu____1763 =
                      let uu____1764 =
                        FStar_Extraction_ML_Util.mlconst_of_const'
                          p.FStar_Syntax_Syntax.p s
                         in
                      FStar_Extraction_ML_Syntax.MLP_Const uu____1764  in
                    (uu____1763, [])  in
                  Some uu____1759  in
                let uu____1769 = ok mlty  in (g, uu____1754, uu____1769)
            | FStar_Syntax_Syntax.Pat_var x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort  in
                let g1 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp
                   in
                let uu____1778 =
                  if imp
                  then None
                  else
                    (let uu____1791 =
                       let uu____1795 =
                         let uu____1796 =
                           FStar_Extraction_ML_Syntax.bv_as_mlident x  in
                         FStar_Extraction_ML_Syntax.MLP_Var uu____1796  in
                       (uu____1795, [])  in
                     Some uu____1791)
                   in
                let uu____1801 = ok mlty  in (g1, uu____1778, uu____1801)
            | FStar_Syntax_Syntax.Pat_wild x when disjunctive_pat ->
                (g, (Some (FStar_Extraction_ML_Syntax.MLP_Wild, [])), true)
            | FStar_Syntax_Syntax.Pat_wild x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort  in
                let g1 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp
                   in
                let uu____1819 =
                  if imp
                  then None
                  else
                    (let uu____1832 =
                       let uu____1836 =
                         let uu____1837 =
                           FStar_Extraction_ML_Syntax.bv_as_mlident x  in
                         FStar_Extraction_ML_Syntax.MLP_Var uu____1837  in
                       (uu____1836, [])  in
                     Some uu____1832)
                   in
                let uu____1842 = ok mlty  in (g1, uu____1819, uu____1842)
            | FStar_Syntax_Syntax.Pat_dot_term uu____1847 -> (g, None, true)
            | FStar_Syntax_Syntax.Pat_cons (f,pats) ->
                let uu____1871 =
                  let uu____1874 = FStar_Extraction_ML_UEnv.lookup_fv g f  in
                  match uu____1874 with
                  | FStar_Util.Inr
                      ({
                         FStar_Extraction_ML_Syntax.expr =
                           FStar_Extraction_ML_Syntax.MLE_Name n1;
                         FStar_Extraction_ML_Syntax.mlty = uu____1878;
                         FStar_Extraction_ML_Syntax.loc = uu____1879;_},ttys,uu____1881)
                      -> (n1, ttys)
                  | uu____1887 -> failwith "Expected a constructor"  in
                (match uu____1871 with
                 | (d,tys) ->
                     let nTyVars = FStar_List.length (Prims.fst tys)  in
                     let uu____1901 = FStar_Util.first_N nTyVars pats  in
                     (match uu____1901 with
                      | (tysVarPats,restPats) ->
                          let f_ty_opt =
                            try
                              let mlty_args =
                                FStar_All.pipe_right tysVarPats
                                  (FStar_List.map
                                     (fun uu____1975  ->
                                        match uu____1975 with
                                        | (p1,uu____1981) ->
                                            (match p1.FStar_Syntax_Syntax.v
                                             with
                                             | FStar_Syntax_Syntax.Pat_dot_term
                                                 (uu____1986,t) ->
                                                 term_as_mlty g t
                                             | uu____1992 ->
                                                 (FStar_Extraction_ML_UEnv.debug
                                                    g
                                                    (fun uu____1994  ->
                                                       let uu____1995 =
                                                         FStar_Syntax_Print.pat_to_string
                                                           p1
                                                          in
                                                       FStar_Util.print1
                                                         "Pattern %s is not extractable"
                                                         uu____1995);
                                                  Prims.raise Un_extractable))))
                                 in
                              let f_ty =
                                FStar_Extraction_ML_Util.subst tys mlty_args
                                 in
                              let uu____1997 =
                                FStar_Extraction_ML_Util.uncurry_mlty_fun
                                  f_ty
                                 in
                              Some uu____1997
                            with | Un_extractable  -> None  in
                          let uu____2012 =
                            FStar_Util.fold_map
                              (fun g1  ->
                                 fun uu____2027  ->
                                   match uu____2027 with
                                   | (p1,imp1) ->
                                       let uu____2038 =
                                         extract_one_pat disjunctive_pat true
                                           g1 p1 None
                                          in
                                       (match uu____2038 with
                                        | (g2,p2,uu____2054) -> (g2, p2))) g
                              tysVarPats
                             in
                          (match uu____2012 with
                           | (g1,tyMLPats) ->
                               let uu____2086 =
                                 FStar_Util.fold_map
                                   (fun uu____2112  ->
                                      fun uu____2113  ->
                                        match (uu____2112, uu____2113) with
                                        | ((g2,f_ty_opt1),(p1,imp1)) ->
                                            let uu____2162 =
                                              match f_ty_opt1 with
                                              | Some (hd1::rest,res) ->
                                                  ((Some (rest, res)),
                                                    (Some hd1))
                                              | uu____2194 -> (None, None)
                                               in
                                            (match uu____2162 with
                                             | (f_ty_opt2,expected_ty) ->
                                                 let uu____2231 =
                                                   extract_one_pat
                                                     disjunctive_pat false g2
                                                     p1 expected_ty
                                                    in
                                                 (match uu____2231 with
                                                  | (g3,p2,uu____2253) ->
                                                      ((g3, f_ty_opt2), p2))))
                                   (g1, f_ty_opt) restPats
                                  in
                               (match uu____2086 with
                                | ((g2,f_ty_opt1),restMLPats) ->
                                    let uu____2314 =
                                      let uu____2320 =
                                        FStar_All.pipe_right
                                          (FStar_List.append tyMLPats
                                             restMLPats)
                                          (FStar_List.collect
                                             (fun uu___134_2345  ->
                                                match uu___134_2345 with
                                                | Some x -> [x]
                                                | uu____2367 -> []))
                                         in
                                      FStar_All.pipe_right uu____2320
                                        FStar_List.split
                                       in
                                    (match uu____2314 with
                                     | (mlPats,when_clauses) ->
                                         let pat_ty_compat =
                                           match f_ty_opt1 with
                                           | Some ([],t) -> ok t
                                           | uu____2406 -> false  in
                                         let uu____2411 =
                                           let uu____2416 =
                                             let uu____2420 =
                                               resugar_pat
                                                 f.FStar_Syntax_Syntax.fv_qual
                                                 (FStar_Extraction_ML_Syntax.MLP_CTor
                                                    (d, mlPats))
                                                in
                                             let uu____2422 =
                                               FStar_All.pipe_right
                                                 when_clauses
                                                 FStar_List.flatten
                                                in
                                             (uu____2420, uu____2422)  in
                                           Some uu____2416  in
                                         (g2, uu____2411, pat_ty_compat))))))
  
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
        let extract_one_pat1 disj g1 p1 expected_t1 =
          let uu____2483 = extract_one_pat disj false g1 p1 expected_t1  in
          match uu____2483 with
          | (g2,Some (x,v1),b) -> (g2, (x, v1), b)
          | uu____2514 -> failwith "Impossible: Unable to translate pattern"
           in
        let mk_when_clause whens =
          match whens with
          | [] -> None
          | hd1::tl1 ->
              let uu____2539 =
                FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd1 tl1
                 in
              Some uu____2539
           in
        match p.FStar_Syntax_Syntax.v with
        | FStar_Syntax_Syntax.Pat_disj [] ->
            failwith "Impossible: Empty disjunctive pattern"
        | FStar_Syntax_Syntax.Pat_disj (p1::pats) ->
            let uu____2565 = extract_one_pat1 true g p1 (Some expected_t)  in
            (match uu____2565 with
             | (g1,p2,b) ->
                 let uu____2588 =
                   FStar_Util.fold_map
                     (fun b1  ->
                        fun p3  ->
                          let uu____2600 =
                            extract_one_pat1 true g1 p3 (Some expected_t)  in
                          match uu____2600 with
                          | (uu____2612,p4,b') -> ((b1 && b'), p4)) b pats
                    in
                 (match uu____2588 with
                  | (b1,ps) ->
                      let ps1 = p2 :: ps  in
                      let uu____2649 =
                        FStar_All.pipe_right ps1
                          (FStar_List.partition
                             (fun uu___135_2677  ->
                                match uu___135_2677 with
                                | (uu____2681,uu____2682::uu____2683) -> true
                                | uu____2686 -> false))
                         in
                      (match uu____2649 with
                       | (ps_when,rest) ->
                           let ps2 =
                             FStar_All.pipe_right ps_when
                               (FStar_List.map
                                  (fun uu____2734  ->
                                     match uu____2734 with
                                     | (x,whens) ->
                                         let uu____2745 =
                                           mk_when_clause whens  in
                                         (x, uu____2745)))
                              in
                           let res =
                             match rest with
                             | [] -> (g1, ps2, b1)
                             | rest1 ->
                                 let uu____2775 =
                                   let uu____2780 =
                                     let uu____2784 =
                                       let uu____2785 =
                                         FStar_List.map Prims.fst rest1  in
                                       FStar_Extraction_ML_Syntax.MLP_Branch
                                         uu____2785
                                        in
                                     (uu____2784, None)  in
                                   uu____2780 :: ps2  in
                                 (g1, uu____2775, b1)
                              in
                           res)))
        | uu____2799 ->
            let uu____2800 = extract_one_pat1 false g p (Some expected_t)  in
            (match uu____2800 with
             | (g1,(p1,whens),b) ->
                 let when_clause = mk_when_clause whens  in
                 (g1, [(p1, when_clause)], b))
  
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
            | FStar_Extraction_ML_Syntax.MLTY_Fun (t0,uu____2882,t1) ->
                let x = FStar_Extraction_ML_Syntax.gensym ()  in
                let uu____2885 =
                  let uu____2891 =
                    let uu____2896 =
                      FStar_All.pipe_left
                        (FStar_Extraction_ML_Syntax.with_ty t0)
                        (FStar_Extraction_ML_Syntax.MLE_Var x)
                       in
                    ((x, t0), uu____2896)  in
                  uu____2891 :: more_args  in
                eta_args uu____2885 t1
            | FStar_Extraction_ML_Syntax.MLTY_Named (uu____2903,uu____2904)
                -> ((FStar_List.rev more_args), t)
            | uu____2916 -> failwith "Impossible: Head type is not an arrow"
             in
          let as_record qual1 e =
            match ((e.FStar_Extraction_ML_Syntax.expr), qual1) with
            | (FStar_Extraction_ML_Syntax.MLE_CTor (uu____2934,args),Some
               (FStar_Syntax_Syntax.Record_ctor (tyname,fields))) ->
                let path =
                  FStar_List.map FStar_Ident.text_of_id tyname.FStar_Ident.ns
                   in
                let fields1 = record_fields fields args  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     e.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_Record (path, fields1))
            | uu____2953 -> e  in
          let resugar_and_maybe_eta qual1 e =
            let uu____2966 = eta_args [] residualType  in
            match uu____2966 with
            | (eargs,tres) ->
                (match eargs with
                 | [] ->
                     let uu____2994 = as_record qual1 e  in
                     FStar_Extraction_ML_Util.resugar_exp uu____2994
                 | uu____2995 ->
                     let uu____3001 = FStar_List.unzip eargs  in
                     (match uu____3001 with
                      | (binders,eargs1) ->
                          (match e.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_CTor (head1,args)
                               ->
                               let body =
                                 let uu____3025 =
                                   let uu____3026 =
                                     FStar_All.pipe_left
                                       (FStar_Extraction_ML_Syntax.with_ty
                                          tres)
                                       (FStar_Extraction_ML_Syntax.MLE_CTor
                                          (head1,
                                            (FStar_List.append args eargs1)))
                                      in
                                   FStar_All.pipe_left (as_record qual1)
                                     uu____3026
                                    in
                                 FStar_All.pipe_left
                                   FStar_Extraction_ML_Util.resugar_exp
                                   uu____3025
                                  in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    e.FStar_Extraction_ML_Syntax.mlty)
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    (binders, body))
                           | uu____3031 ->
                               failwith "Impossible: Not a constructor")))
             in
          match ((mlAppExpr.FStar_Extraction_ML_Syntax.expr), qual) with
          | (uu____3033,None ) -> mlAppExpr
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____3036;
                FStar_Extraction_ML_Syntax.loc = uu____3037;_},mle::args),Some
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
                | uu____3055 ->
                    let uu____3057 =
                      let uu____3061 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj
                         in
                      (uu____3061, args)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____3057
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
              let uu____3076 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____3076
          | (FStar_Extraction_ML_Syntax.MLE_Name mlp,Some
             (FStar_Syntax_Syntax.Data_ctor ))
            |(FStar_Extraction_ML_Syntax.MLE_Name mlp,Some
              (FStar_Syntax_Syntax.Record_ctor _)) ->
              let uu____3082 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____3082
          | uu____3084 -> mlAppExpr
  
let maybe_downgrade_eff :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.e_tag ->
      FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.e_tag
  =
  fun g  ->
    fun f  ->
      fun t  ->
        let uu____3097 =
          (f = FStar_Extraction_ML_Syntax.E_GHOST) &&
            (type_leq g t FStar_Extraction_ML_Syntax.ml_unit_ty)
           in
        if uu____3097 then FStar_Extraction_ML_Syntax.E_PURE else f
  
let rec term_as_mlexpr :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag *
        FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun t  ->
      let uu____3138 = term_as_mlexpr' g t  in
      match uu____3138 with
      | (e,tag,ty) ->
          let tag1 = maybe_downgrade_eff g tag ty  in
          (FStar_Extraction_ML_UEnv.debug g
             (fun u  ->
                let uu____3151 =
                  let uu____3152 = FStar_Syntax_Print.tag_of_term t  in
                  let uu____3153 = FStar_Syntax_Print.term_to_string t  in
                  let uu____3154 =
                    FStar_Extraction_ML_Code.string_of_mlty
                      g.FStar_Extraction_ML_UEnv.currentModule ty
                     in
                  FStar_Util.format4
                    "term_as_mlexpr (%s) :  %s has ML type %s and effect %s\n"
                    uu____3152 uu____3153 uu____3154
                    (FStar_Extraction_ML_Util.eff_to_string tag1)
                   in
                FStar_Util.print_string uu____3151);
           erase g e ty tag1)

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
          let uu____3161 = check_term_as_mlexpr' g t f ty  in
          match uu____3161 with
          | (e,t1) ->
              let uu____3168 = erase g e t1 f  in
              (match uu____3168 with | (r,uu____3175,t2) -> (r, t2))

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
          let uu____3183 = term_as_mlexpr g e0  in
          match uu____3183 with
          | (e,tag,t) ->
              let tag1 = maybe_downgrade_eff g tag t  in
              if FStar_Extraction_ML_Util.eff_leq tag1 f
              then
                let uu____3195 = maybe_coerce g e t ty  in (uu____3195, ty)
              else err_unexpected_eff e0 f tag1

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
           let uu____3206 =
             let uu____3207 =
               FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos  in
             let uu____3208 = FStar_Syntax_Print.tag_of_term top  in
             let uu____3209 = FStar_Syntax_Print.term_to_string top  in
             FStar_Util.format3 "%s: term_as_mlexpr' (%s) :  %s \n"
               uu____3207 uu____3208 uu____3209
              in
           FStar_Util.print_string uu____3206);
      (let t = FStar_Syntax_Subst.compress top  in
       match t.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_unknown 
         |FStar_Syntax_Syntax.Tm_delayed _
          |FStar_Syntax_Syntax.Tm_uvar _|FStar_Syntax_Syntax.Tm_bvar _ ->
           let uu____3217 =
             let uu____3218 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____3218
              in
           failwith uu____3217
       | FStar_Syntax_Syntax.Tm_type _
         |FStar_Syntax_Syntax.Tm_refine _|FStar_Syntax_Syntax.Tm_arrow _ ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Mutable_alloc ))
           ->
           let uu____3230 = term_as_mlexpr' g t1  in
           (match uu____3230 with
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
            | uu____3257 -> failwith "impossible")
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_monadic (m,uu____3266)) ->
           let t2 = FStar_Syntax_Subst.compress t1  in
           (match t2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) when
                FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname ->
                let ed =
                  FStar_TypeChecker_Env.get_effect_decl
                    g.FStar_Extraction_ML_UEnv.tcenv m
                   in
                let uu____3290 =
                  let uu____3291 =
                    FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                     in
                  FStar_All.pipe_right uu____3291 Prims.op_Negation  in
                if uu____3290
                then term_as_mlexpr' g t2
                else
                  (let ml_result_ty_1 =
                     term_as_mlty g lb.FStar_Syntax_Syntax.lbtyp  in
                   let uu____3298 =
                     term_as_mlexpr g lb.FStar_Syntax_Syntax.lbdef  in
                   match uu____3298 with
                   | (comp_1,uu____3306,uu____3307) ->
                       let uu____3308 =
                         let k =
                           let uu____3312 =
                             let uu____3316 =
                               let uu____3317 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               FStar_All.pipe_right uu____3317
                                 FStar_Syntax_Syntax.mk_binder
                                in
                             [uu____3316]  in
                           FStar_Syntax_Util.abs uu____3312 body None  in
                         let uu____3323 = term_as_mlexpr g k  in
                         match uu____3323 with
                         | (ml_k,uu____3330,t_k) ->
                             let m_2 =
                               match t_k with
                               | FStar_Extraction_ML_Syntax.MLTY_Fun
                                   (uu____3333,uu____3334,m_2) -> m_2
                               | uu____3336 -> failwith "Impossible"  in
                             (ml_k, m_2)
                          in
                       (match uu____3308 with
                        | (ml_k,ty) ->
                            let bind1 =
                              let uu____3343 =
                                let uu____3344 =
                                  let uu____3345 =
                                    FStar_Extraction_ML_UEnv.monad_op_name ed
                                      "bind"
                                     in
                                  FStar_All.pipe_right uu____3345 Prims.fst
                                   in
                                FStar_Extraction_ML_Syntax.MLE_Name
                                  uu____3344
                                 in
                              FStar_All.pipe_left
                                (FStar_Extraction_ML_Syntax.with_ty
                                   FStar_Extraction_ML_Syntax.MLTY_Top)
                                uu____3343
                               in
                            let uu____3350 =
                              FStar_All.pipe_left
                                (FStar_Extraction_ML_Syntax.with_ty ty)
                                (FStar_Extraction_ML_Syntax.MLE_App
                                   (bind1, [comp_1; ml_k]))
                               in
                            (uu____3350, FStar_Extraction_ML_Syntax.E_IMPURE,
                              ty)))
            | uu____3352 -> term_as_mlexpr' g t2)
       | FStar_Syntax_Syntax.Tm_meta (t1,_)|FStar_Syntax_Syntax.Tm_uinst
         (t1,_) -> term_as_mlexpr' g t1
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____3365 =
             FStar_TypeChecker_TcTerm.type_of_tot_term
               g.FStar_Extraction_ML_UEnv.tcenv t
              in
           (match uu____3365 with
            | (uu____3372,ty,uu____3374) ->
                let ml_ty = term_as_mlty g ty  in
                let uu____3376 =
                  let uu____3377 =
                    let uu____3378 =
                      FStar_Extraction_ML_Util.mlconst_of_const'
                        t.FStar_Syntax_Syntax.pos c
                       in
                    FStar_All.pipe_left
                      (fun _0_31  ->
                         FStar_Extraction_ML_Syntax.MLE_Const _0_31)
                      uu____3378
                     in
                  FStar_Extraction_ML_Syntax.with_ty ml_ty uu____3377  in
                (uu____3376, FStar_Extraction_ML_Syntax.E_PURE, ml_ty))
       | FStar_Syntax_Syntax.Tm_name _|FStar_Syntax_Syntax.Tm_fvar _ ->
           let uu____3381 = is_type g t  in
           if uu____3381
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____3386 = FStar_Extraction_ML_UEnv.lookup_term g t  in
              match uu____3386 with
              | (FStar_Util.Inl uu____3393,uu____3394) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | (FStar_Util.Inr (x,mltys,uu____3413),qual) ->
                  (match mltys with
                   | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                       ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | ([],t1) ->
                       let uu____3436 =
                         maybe_eta_data_and_project_record g qual t1 x  in
                       (uu____3436, FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | uu____3437 -> err_uninst g t mltys t))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,copt) ->
           let uu____3466 = FStar_Syntax_Subst.open_term bs body  in
           (match uu____3466 with
            | (bs1,body1) ->
                let uu____3474 = binders_as_ml_binders g bs1  in
                (match uu____3474 with
                 | (ml_bs,env) ->
                     let uu____3491 = term_as_mlexpr env body1  in
                     (match uu____3491 with
                      | (ml_body,f,t1) ->
                          let uu____3501 =
                            FStar_List.fold_right
                              (fun uu____3508  ->
                                 fun uu____3509  ->
                                   match (uu____3508, uu____3509) with
                                   | ((uu____3520,targ),(f1,t2)) ->
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         (FStar_Extraction_ML_Syntax.MLTY_Fun
                                            (targ, f1, t2)))) ml_bs (f, t1)
                             in
                          (match uu____3501 with
                           | (f1,tfun) ->
                               let uu____3533 =
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty tfun)
                                   (FStar_Extraction_ML_Syntax.MLE_Fun
                                      (ml_bs, ml_body))
                                  in
                               (uu____3533, f1, tfun)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.tk = uu____3537;
              FStar_Syntax_Syntax.pos = uu____3538;
              FStar_Syntax_Syntax.vars = uu____3539;_},t1::[])
           ->
           let uu____3562 = term_as_mlexpr' g (Prims.fst t1)  in
           (match uu____3562 with
            | (ml,e_tag,mlty) ->
                (ml, FStar_Extraction_ML_Syntax.E_PURE, mlty))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____3574);
              FStar_Syntax_Syntax.tk = uu____3575;
              FStar_Syntax_Syntax.pos = uu____3576;
              FStar_Syntax_Syntax.vars = uu____3577;_},t1::[])
           ->
           let uu____3600 = term_as_mlexpr' g (Prims.fst t1)  in
           (match uu____3600 with
            | (ml,e_tag,mlty) ->
                (ml, FStar_Extraction_ML_Syntax.E_IMPURE, mlty))
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let is_total uu___137_3636 =
             match uu___137_3636 with
             | FStar_Util.Inl l -> FStar_Syntax_Util.is_total_lcomp l
             | FStar_Util.Inr (l,flags) ->
                 (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid)
                   ||
                   (FStar_All.pipe_right flags
                      (FStar_List.existsb
                         (fun uu___136_3654  ->
                            match uu___136_3654 with
                            | FStar_Syntax_Syntax.TOTAL  -> true
                            | uu____3655 -> false)))
              in
           let uu____3656 =
             let uu____3659 =
               let uu____3660 = FStar_Syntax_Subst.compress head1  in
               uu____3660.FStar_Syntax_Syntax.n  in
             ((head1.FStar_Syntax_Syntax.n), uu____3659)  in
           (match uu____3656 with
            | (FStar_Syntax_Syntax.Tm_uvar uu____3666,uu____3667) ->
                let t1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.Iota;
                    FStar_TypeChecker_Normalize.Zeta;
                    FStar_TypeChecker_Normalize.EraseUniverses;
                    FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                    g.FStar_Extraction_ML_UEnv.tcenv t
                   in
                term_as_mlexpr' g t1
            | (uu____3677,FStar_Syntax_Syntax.Tm_abs (bs,uu____3679,Some lc))
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
                term_as_mlexpr' g t1
            | uu____3708 ->
                let rec extract_app is_data uu____3736 uu____3737 restArgs =
                  match (uu____3736, uu____3737) with
                  | ((mlhead,mlargs_f),(f,t1)) ->
                      (match (restArgs, t1) with
                       | ([],uu____3785) ->
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
                                | uu____3799 -> false)
                              in
                           let uu____3800 =
                             if evaluation_order_guaranteed
                             then
                               let uu____3813 =
                                 FStar_All.pipe_right
                                   (FStar_List.rev mlargs_f)
                                   (FStar_List.map Prims.fst)
                                  in
                               ([], uu____3813)
                             else
                               FStar_List.fold_left
                                 (fun uu____3838  ->
                                    fun uu____3839  ->
                                      match (uu____3838, uu____3839) with
                                      | ((lbs,out_args),(arg,f1)) ->
                                          if
                                            (f1 =
                                               FStar_Extraction_ML_Syntax.E_PURE)
                                              ||
                                              (f1 =
                                                 FStar_Extraction_ML_Syntax.E_GHOST)
                                          then (lbs, (arg :: out_args))
                                          else
                                            (let x =
                                               FStar_Extraction_ML_Syntax.gensym
                                                 ()
                                                in
                                             let uu____3894 =
                                               let uu____3896 =
                                                 FStar_All.pipe_left
                                                   (FStar_Extraction_ML_Syntax.with_ty
                                                      arg.FStar_Extraction_ML_Syntax.mlty)
                                                   (FStar_Extraction_ML_Syntax.MLE_Var
                                                      x)
                                                  in
                                               uu____3896 :: out_args  in
                                             (((x, arg) :: lbs), uu____3894)))
                                 ([], []) mlargs_f
                              in
                           (match uu____3800 with
                            | (lbs,mlargs) ->
                                let app =
                                  let uu____3923 =
                                    FStar_All.pipe_left
                                      (FStar_Extraction_ML_Syntax.with_ty t1)
                                      (FStar_Extraction_ML_Syntax.MLE_App
                                         (mlhead, mlargs))
                                     in
                                  FStar_All.pipe_left
                                    (maybe_eta_data_and_project_record g
                                       is_data t1) uu____3923
                                   in
                                let l_app =
                                  FStar_List.fold_right
                                    (fun uu____3928  ->
                                       fun out  ->
                                         match uu____3928 with
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
                                (l_app, f, t1))
                       | ((arg,uu____3941)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                          (formal_t,f',t2)) when is_type g arg ->
                           let uu____3959 =
                             type_leq g formal_t
                               FStar_Extraction_ML_Syntax.ml_unit_ty
                              in
                           if uu____3959
                           then
                             let uu____3963 =
                               let uu____3966 =
                                 FStar_Extraction_ML_Util.join
                                   arg.FStar_Syntax_Syntax.pos f f'
                                  in
                               (uu____3966, t2)  in
                             extract_app is_data
                               (mlhead,
                                 ((FStar_Extraction_ML_Syntax.ml_unit,
                                    FStar_Extraction_ML_Syntax.E_PURE) ::
                                 mlargs_f)) uu____3963 rest
                           else
                             (let uu____3973 =
                                let uu____3974 =
                                  FStar_Extraction_ML_Code.string_of_mlexpr
                                    g.FStar_Extraction_ML_UEnv.currentModule
                                    mlhead
                                   in
                                let uu____3975 =
                                  FStar_Syntax_Print.term_to_string arg  in
                                let uu____3976 =
                                  FStar_Syntax_Print.tag_of_term arg  in
                                let uu____3977 =
                                  FStar_Extraction_ML_Code.string_of_mlty
                                    g.FStar_Extraction_ML_UEnv.currentModule
                                    formal_t
                                   in
                                FStar_Util.format4
                                  "Impossible: ill-typed application:\n\thead=%s, arg=%s, tag=%s\n\texpected type unit, got %s"
                                  uu____3974 uu____3975 uu____3976 uu____3977
                                 in
                              failwith uu____3973)
                       | ((e0,uu____3982)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                          (tExpected,f',t2)) ->
                           let r = e0.FStar_Syntax_Syntax.pos  in
                           let uu____4001 = term_as_mlexpr g e0  in
                           (match uu____4001 with
                            | (e01,f0,tInferred) ->
                                let e02 =
                                  maybe_coerce g e01 tInferred tExpected  in
                                let uu____4012 =
                                  let uu____4015 =
                                    FStar_Extraction_ML_Util.join_l r
                                      [f; f'; f0]
                                     in
                                  (uu____4015, t2)  in
                                extract_app is_data
                                  (mlhead, ((e02, f0) :: mlargs_f))
                                  uu____4012 rest)
                       | uu____4021 ->
                           let uu____4028 =
                             FStar_Extraction_ML_Util.udelta_unfold g t1  in
                           (match uu____4028 with
                            | Some t2 ->
                                extract_app is_data (mlhead, mlargs_f)
                                  (f, t2) restArgs
                            | None  ->
                                err_ill_typed_application g top restArgs t1))
                   in
                let extract_app_maybe_projector is_data mlhead uu____4064
                  args1 =
                  match uu____4064 with
                  | (f,t1) ->
                      (match is_data with
                       | Some (FStar_Syntax_Syntax.Record_projector
                           uu____4083) ->
                           let rec remove_implicits args2 f1 t2 =
                             match (args2, t2) with
                             | ((a0,Some (FStar_Syntax_Syntax.Implicit
                                 uu____4133))::args3,FStar_Extraction_ML_Syntax.MLTY_Fun
                                (uu____4135,f',t3)) ->
                                 let uu____4160 =
                                   FStar_Extraction_ML_Util.join
                                     a0.FStar_Syntax_Syntax.pos f1 f'
                                    in
                                 remove_implicits args3 uu____4160 t3
                             | uu____4161 -> (args2, f1, t2)  in
                           let uu____4176 = remove_implicits args1 f t1  in
                           (match uu____4176 with
                            | (args2,f1,t2) ->
                                extract_app is_data (mlhead, []) (f1, t2)
                                  args2)
                       | uu____4209 ->
                           extract_app is_data (mlhead, []) (f, t1) args1)
                   in
                let uu____4216 = is_type g t  in
                if uu____4216
                then
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
                else
                  (let head2 = FStar_Syntax_Util.un_uinst head1  in
                   match head2.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_name _
                     |FStar_Syntax_Syntax.Tm_fvar _ ->
                       let uu____4227 =
                         let uu____4234 =
                           FStar_Extraction_ML_UEnv.lookup_term g head2  in
                         match uu____4234 with
                         | (FStar_Util.Inr u,q) -> (u, q)
                         | uu____4267 -> failwith "FIXME Ty"  in
                       (match uu____4227 with
                        | ((head_ml,(vars,t1),inst_ok),qual) ->
                            let has_typ_apps =
                              match args with
                              | (a,uu____4296)::uu____4297 -> is_type g a
                              | uu____4311 -> false  in
                            let uu____4317 =
                              match vars with
                              | uu____4334::uu____4335 when
                                  (Prims.op_Negation has_typ_apps) && inst_ok
                                  -> (head_ml, t1, args)
                              | uu____4342 ->
                                  let n1 = FStar_List.length vars  in
                                  if n1 <= (FStar_List.length args)
                                  then
                                    let uu____4362 =
                                      FStar_Util.first_N n1 args  in
                                    (match uu____4362 with
                                     | (prefix1,rest) ->
                                         let prefixAsMLTypes =
                                           FStar_List.map
                                             (fun uu____4415  ->
                                                match uu____4415 with
                                                | (x,uu____4419) ->
                                                    term_as_mlty g x) prefix1
                                            in
                                         let t2 =
                                           instantiate (vars, t1)
                                             prefixAsMLTypes
                                            in
                                         let head3 =
                                           match head_ml.FStar_Extraction_ML_Syntax.expr
                                           with
                                           | FStar_Extraction_ML_Syntax.MLE_Name
                                             _
                                             |FStar_Extraction_ML_Syntax.MLE_Var
                                             _ ->
                                               let uu___141_4424 = head_ml
                                                  in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (uu___141_4424.FStar_Extraction_ML_Syntax.expr);
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   = t2;
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___141_4424.FStar_Extraction_ML_Syntax.loc)
                                               }
                                           | FStar_Extraction_ML_Syntax.MLE_App
                                               (head3,{
                                                        FStar_Extraction_ML_Syntax.expr
                                                          =
                                                          FStar_Extraction_ML_Syntax.MLE_Const
                                                          (FStar_Extraction_ML_Syntax.MLC_Unit
                                                          );
                                                        FStar_Extraction_ML_Syntax.mlty
                                                          = uu____4426;
                                                        FStar_Extraction_ML_Syntax.loc
                                                          = uu____4427;_}::[])
                                               ->
                                               FStar_All.pipe_right
                                                 (FStar_Extraction_ML_Syntax.MLE_App
                                                    ((let uu___142_4430 =
                                                        head3  in
                                                      {
                                                        FStar_Extraction_ML_Syntax.expr
                                                          =
                                                          (uu___142_4430.FStar_Extraction_ML_Syntax.expr);
                                                        FStar_Extraction_ML_Syntax.mlty
                                                          =
                                                          (FStar_Extraction_ML_Syntax.MLTY_Fun
                                                             (FStar_Extraction_ML_Syntax.ml_unit_ty,
                                                               FStar_Extraction_ML_Syntax.E_PURE,
                                                               t2));
                                                        FStar_Extraction_ML_Syntax.loc
                                                          =
                                                          (uu___142_4430.FStar_Extraction_ML_Syntax.loc)
                                                      }),
                                                      [FStar_Extraction_ML_Syntax.ml_unit]))
                                                 (FStar_Extraction_ML_Syntax.with_ty
                                                    t2)
                                           | uu____4431 ->
                                               failwith
                                                 "Impossible: Unexpected head term"
                                            in
                                         (head3, t2, rest))
                                  else err_uninst g head2 (vars, t1) top
                               in
                            (match uu____4317 with
                             | (head_ml1,head_t,args1) ->
                                 (match args1 with
                                  | [] ->
                                      let uu____4469 =
                                        maybe_eta_data_and_project_record g
                                          qual head_t head_ml1
                                         in
                                      (uu____4469,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        head_t)
                                  | uu____4470 ->
                                      extract_app_maybe_projector qual
                                        head_ml1
                                        (FStar_Extraction_ML_Syntax.E_PURE,
                                          head_t) args1)))
                   | uu____4476 ->
                       let uu____4477 = term_as_mlexpr g head2  in
                       (match uu____4477 with
                        | (head3,f,t1) ->
                            extract_app_maybe_projector None head3 (f, t1)
                              args)))
       | FStar_Syntax_Syntax.Tm_ascribed (e0,tc,f) ->
           let t1 =
             match tc with
             | FStar_Util.Inl t1 -> term_as_mlty g t1
             | FStar_Util.Inr c ->
                 let uu____4523 =
                   FStar_TypeChecker_Env.result_typ
                     g.FStar_Extraction_ML_UEnv.tcenv c
                    in
                 term_as_mlty g uu____4523
              in
           let f1 =
             match f with
             | None  -> failwith "Ascription node with an empty effect label"
             | Some l -> effect_as_etag g l  in
           let uu____4526 = check_term_as_mlexpr g e0 f1 t1  in
           (match uu____4526 with | (e,t2) -> (e, f1, t2))
       | FStar_Syntax_Syntax.Tm_let ((is_rec,lbs),e') ->
           let top_level = FStar_Syntax_Syntax.is_top_level lbs  in
           let uu____4547 =
             if is_rec
             then FStar_Syntax_Subst.open_let_rec lbs e'
             else
               (let uu____4555 = FStar_Syntax_Syntax.is_top_level lbs  in
                if uu____4555
                then (lbs, e')
                else
                  (let lb = FStar_List.hd lbs  in
                   let x =
                     let uu____4565 =
                       FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                     FStar_Syntax_Syntax.freshen_bv uu____4565  in
                   let lb1 =
                     let uu___143_4567 = lb  in
                     {
                       FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                       FStar_Syntax_Syntax.lbunivs =
                         (uu___143_4567.FStar_Syntax_Syntax.lbunivs);
                       FStar_Syntax_Syntax.lbtyp =
                         (uu___143_4567.FStar_Syntax_Syntax.lbtyp);
                       FStar_Syntax_Syntax.lbeff =
                         (uu___143_4567.FStar_Syntax_Syntax.lbeff);
                       FStar_Syntax_Syntax.lbdef =
                         (uu___143_4567.FStar_Syntax_Syntax.lbdef)
                     }  in
                   let e'1 =
                     FStar_Syntax_Subst.subst
                       [FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x)] e'
                      in
                   ([lb1], e'1)))
              in
           (match uu____4547 with
            | (lbs1,e'1) ->
                let lbs2 =
                  if top_level
                  then
                    FStar_All.pipe_right lbs1
                      (FStar_List.map
                         (fun lb  ->
                            let tcenv =
                              let uu____4584 =
                                FStar_Ident.lid_of_path
                                  (FStar_List.append
                                     (Prims.fst
                                        g.FStar_Extraction_ML_UEnv.currentModule)
                                     [Prims.snd
                                        g.FStar_Extraction_ML_UEnv.currentModule])
                                  FStar_Range.dummyRange
                                 in
                              FStar_TypeChecker_Env.set_current_module
                                g.FStar_Extraction_ML_UEnv.tcenv uu____4584
                               in
                            FStar_Extraction_ML_UEnv.debug g
                              (fun uu____4588  ->
                                 FStar_Options.set_option "debug_level"
                                   (FStar_Options.List
                                      [FStar_Options.String "Norm";
                                      FStar_Options.String "Extraction"]));
                            (let lbdef =
                               let uu____4592 = FStar_Options.ml_ish ()  in
                               if uu____4592
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
                             let uu___144_4596 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___144_4596.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___144_4596.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___144_4596.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___144_4596.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef
                             })))
                  else lbs1  in
                let maybe_generalize uu____4610 =
                  match uu____4610 with
                  | { FStar_Syntax_Syntax.lbname = lbname_;
                      FStar_Syntax_Syntax.lbunivs = uu____4621;
                      FStar_Syntax_Syntax.lbtyp = t1;
                      FStar_Syntax_Syntax.lbeff = lbeff;
                      FStar_Syntax_Syntax.lbdef = e;_} ->
                      let f_e = effect_as_etag g lbeff  in
                      let t2 = FStar_Syntax_Subst.compress t1  in
                      (match t2.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                           let uu____4664 = FStar_List.hd bs  in
                           FStar_All.pipe_right uu____4664 (is_type_binder g)
                           ->
                           let uu____4671 = FStar_Syntax_Subst.open_comp bs c
                              in
                           (match uu____4671 with
                            | (bs1,c1) ->
                                let uu____4685 =
                                  let uu____4688 =
                                    FStar_Util.prefix_until
                                      (fun x  ->
                                         let uu____4706 = is_type_binder g x
                                            in
                                         Prims.op_Negation uu____4706) bs1
                                     in
                                  match uu____4688 with
                                  | None  ->
                                      let uu____4720 =
                                        FStar_TypeChecker_Env.result_typ
                                          g.FStar_Extraction_ML_UEnv.tcenv c1
                                         in
                                      (bs1, uu____4720)
                                  | Some (bs2,b,rest) ->
                                      let uu____4751 =
                                        FStar_Syntax_Util.arrow (b :: rest)
                                          c1
                                         in
                                      (bs2, uu____4751)
                                   in
                                (match uu____4685 with
                                 | (tbinders,tbody) ->
                                     let n_tbinders =
                                       FStar_List.length tbinders  in
                                     let e1 =
                                       let uu____4773 = normalize_abs e  in
                                       FStar_All.pipe_right uu____4773
                                         FStar_Syntax_Util.unmeta
                                        in
                                     (match e1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Tm_abs
                                          (bs2,body,uu____4785) ->
                                          let uu____4808 =
                                            FStar_Syntax_Subst.open_term bs2
                                              body
                                             in
                                          (match uu____4808 with
                                           | (bs3,body1) ->
                                               if
                                                 n_tbinders <=
                                                   (FStar_List.length bs3)
                                               then
                                                 let uu____4838 =
                                                   FStar_Util.first_N
                                                     n_tbinders bs3
                                                    in
                                                 (match uu____4838 with
                                                  | (targs,rest_args) ->
                                                      let expected_source_ty
                                                        =
                                                        let s =
                                                          FStar_List.map2
                                                            (fun uu____4881 
                                                               ->
                                                               fun uu____4882
                                                                  ->
                                                                 match 
                                                                   (uu____4881,
                                                                    uu____4882)
                                                                 with
                                                                 | ((x,uu____4892),
                                                                    (y,uu____4894))
                                                                    ->
                                                                    let uu____4899
                                                                    =
                                                                    let uu____4904
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    y  in
                                                                    (x,
                                                                    uu____4904)
                                                                     in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____4899)
                                                            tbinders targs
                                                           in
                                                        FStar_Syntax_Subst.subst
                                                          s tbody
                                                         in
                                                      let env =
                                                        FStar_List.fold_left
                                                          (fun env  ->
                                                             fun uu____4909 
                                                               ->
                                                               match uu____4909
                                                               with
                                                               | (a,uu____4913)
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
                                                        let uu____4921 =
                                                          FStar_All.pipe_right
                                                            targs
                                                            (FStar_List.map
                                                               (fun
                                                                  uu____4935 
                                                                  ->
                                                                  match uu____4935
                                                                  with
                                                                  | (x,uu____4941)
                                                                    ->
                                                                    FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                                    x))
                                                           in
                                                        (uu____4921,
                                                          expected_t)
                                                         in
                                                      let add_unit =
                                                        match rest_args with
                                                        | [] ->
                                                            let uu____4948 =
                                                              is_fstar_value
                                                                body1
                                                               in
                                                            Prims.op_Negation
                                                              uu____4948
                                                        | uu____4949 -> false
                                                         in
                                                      let rest_args1 =
                                                        if add_unit
                                                        then unit_binder ::
                                                          rest_args
                                                        else rest_args  in
                                                      let body2 =
                                                        match rest_args1 with
                                                        | [] -> body1
                                                        | uu____4958 ->
                                                            FStar_Syntax_Util.abs
                                                              rest_args1
                                                              body1 None
                                                         in
                                                      (lbname_, f_e,
                                                        (t2,
                                                          (targs, polytype)),
                                                        add_unit, body2))
                                               else
                                                 failwith
                                                   "Not enough type binders")
                                      | FStar_Syntax_Syntax.Tm_uinst _
                                        |FStar_Syntax_Syntax.Tm_fvar _
                                         |FStar_Syntax_Syntax.Tm_name _ ->
                                          let env =
                                            FStar_List.fold_left
                                              (fun env  ->
                                                 fun uu____5014  ->
                                                   match uu____5014 with
                                                   | (a,uu____5018) ->
                                                       FStar_Extraction_ML_UEnv.extend_ty
                                                         env a None) g
                                              tbinders
                                             in
                                          let expected_t =
                                            term_as_mlty env tbody  in
                                          let polytype =
                                            let uu____5026 =
                                              FStar_All.pipe_right tbinders
                                                (FStar_List.map
                                                   (fun uu____5037  ->
                                                      match uu____5037 with
                                                      | (x,uu____5043) ->
                                                          FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                            x))
                                               in
                                            (uu____5026, expected_t)  in
                                          let args =
                                            FStar_All.pipe_right tbinders
                                              (FStar_List.map
                                                 (fun uu____5052  ->
                                                    match uu____5052 with
                                                    | (bv,uu____5056) ->
                                                        let uu____5057 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            bv
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____5057
                                                          FStar_Syntax_Syntax.as_arg))
                                             in
                                          let e2 =
                                            (FStar_Syntax_Syntax.mk
                                               (FStar_Syntax_Syntax.Tm_app
                                                  (e1, args))) None
                                              e1.FStar_Syntax_Syntax.pos
                                             in
                                          (lbname_, f_e,
                                            (t2, (tbinders, polytype)),
                                            false, e2)
                                      | uu____5095 ->
                                          err_value_restriction e1)))
                       | uu____5105 ->
                           let expected_t = term_as_mlty g t2  in
                           (lbname_, f_e, (t2, ([], ([], expected_t))),
                             false, e))
                   in
                let check_lb env uu____5162 =
                  match uu____5162 with
                  | (nm,(lbname,f,(t1,(targs,polytype)),add_unit,e)) ->
                      let env1 =
                        FStar_List.fold_left
                          (fun env1  ->
                             fun uu____5233  ->
                               match uu____5233 with
                               | (a,uu____5237) ->
                                   FStar_Extraction_ML_UEnv.extend_ty env1 a
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
                      let uu____5240 =
                        check_term_as_mlexpr env1 e f expected_t  in
                      (match uu____5240 with
                       | (e1,uu____5246) ->
                           let f1 = maybe_downgrade_eff env1 f expected_t  in
                           (f1,
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
                let lbs3 =
                  FStar_All.pipe_right lbs2 (FStar_List.map maybe_generalize)
                   in
                let uu____5281 =
                  FStar_List.fold_right
                    (fun lb  ->
                       fun uu____5320  ->
                         match uu____5320 with
                         | (env,lbs4) ->
                             let uu____5384 = lb  in
                             (match uu____5384 with
                              | (lbname,uu____5409,(t1,(uu____5411,polytype)),add_unit,uu____5414)
                                  ->
                                  let uu____5421 =
                                    FStar_Extraction_ML_UEnv.extend_lb env
                                      lbname t1 polytype add_unit true
                                     in
                                  (match uu____5421 with
                                   | (env1,nm) -> (env1, ((nm, lb) :: lbs4)))))
                    lbs3 (g, [])
                   in
                (match uu____5281 with
                 | (env_body,lbs4) ->
                     let env_def = if is_rec then env_body else g  in
                     let lbs5 =
                       FStar_All.pipe_right lbs4
                         (FStar_List.map (check_lb env_def))
                        in
                     let e'_rng = e'1.FStar_Syntax_Syntax.pos  in
                     let uu____5564 = term_as_mlexpr env_body e'1  in
                     (match uu____5564 with
                      | (e'2,f',t') ->
                          let f =
                            let uu____5575 =
                              let uu____5577 = FStar_List.map Prims.fst lbs5
                                 in
                              f' :: uu____5577  in
                            FStar_Extraction_ML_Util.join_l e'_rng uu____5575
                             in
                          let is_rec1 =
                            if is_rec = true
                            then FStar_Extraction_ML_Syntax.Rec
                            else FStar_Extraction_ML_Syntax.NonRec  in
                          let uu____5583 =
                            let uu____5584 =
                              let uu____5585 =
                                let uu____5586 =
                                  FStar_List.map Prims.snd lbs5  in
                                (is_rec1, [], uu____5586)  in
                              mk_MLE_Let top_level uu____5585 e'2  in
                            let uu____5592 =
                              FStar_Extraction_ML_Util.mlloc_of_range
                                t.FStar_Syntax_Syntax.pos
                               in
                            FStar_Extraction_ML_Syntax.with_ty_loc t'
                              uu____5584 uu____5592
                             in
                          (uu____5583, f, t'))))
       | FStar_Syntax_Syntax.Tm_match (scrutinee,pats) ->
           let uu____5621 = term_as_mlexpr g scrutinee  in
           (match uu____5621 with
            | (e,f_e,t_e) ->
                let uu____5631 = check_pats_for_ite pats  in
                (match uu____5631 with
                 | (b,then_e,else_e) ->
                     let no_lift x t1 = x  in
                     if b
                     then
                       (match (then_e, else_e) with
                        | (Some then_e1,Some else_e1) ->
                            let uu____5666 = term_as_mlexpr g then_e1  in
                            (match uu____5666 with
                             | (then_mle,f_then,t_then) ->
                                 let uu____5676 = term_as_mlexpr g else_e1
                                    in
                                 (match uu____5676 with
                                  | (else_mle,f_else,t_else) ->
                                      let uu____5686 =
                                        let uu____5693 =
                                          type_leq g t_then t_else  in
                                        if uu____5693
                                        then (t_else, no_lift)
                                        else
                                          (let uu____5705 =
                                             type_leq g t_else t_then  in
                                           if uu____5705
                                           then (t_then, no_lift)
                                           else
                                             (FStar_Extraction_ML_Syntax.MLTY_Top,
                                               FStar_Extraction_ML_Syntax.apply_obj_repr))
                                         in
                                      (match uu____5686 with
                                       | (t_branch,maybe_lift1) ->
                                           let uu____5734 =
                                             let uu____5735 =
                                               let uu____5736 =
                                                 let uu____5741 =
                                                   maybe_lift1 then_mle
                                                     t_then
                                                    in
                                                 let uu____5742 =
                                                   let uu____5744 =
                                                     maybe_lift1 else_mle
                                                       t_else
                                                      in
                                                   Some uu____5744  in
                                                 (e, uu____5741, uu____5742)
                                                  in
                                               FStar_Extraction_ML_Syntax.MLE_If
                                                 uu____5736
                                                in
                                             FStar_All.pipe_left
                                               (FStar_Extraction_ML_Syntax.with_ty
                                                  t_branch) uu____5735
                                              in
                                           let uu____5746 =
                                             FStar_Extraction_ML_Util.join
                                               then_e1.FStar_Syntax_Syntax.pos
                                               f_then f_else
                                              in
                                           (uu____5734, uu____5746, t_branch))))
                        | uu____5747 ->
                            failwith
                              "ITE pats matched but then and else expressions not found?")
                     else
                       (let uu____5756 =
                          FStar_All.pipe_right pats
                            (FStar_Util.fold_map
                               (fun compat  ->
                                  fun br  ->
                                    let uu____5806 =
                                      FStar_Syntax_Subst.open_branch br  in
                                    match uu____5806 with
                                    | (pat,when_opt,branch1) ->
                                        let uu____5836 =
                                          extract_pat g pat t_e  in
                                        (match uu____5836 with
                                         | (env,p,pat_t_compat) ->
                                             let uu____5867 =
                                               match when_opt with
                                               | None  ->
                                                   (None,
                                                     FStar_Extraction_ML_Syntax.E_PURE)
                                               | Some w ->
                                                   let uu____5882 =
                                                     term_as_mlexpr env w  in
                                                   (match uu____5882 with
                                                    | (w1,f_w,t_w) ->
                                                        let w2 =
                                                          maybe_coerce env w1
                                                            t_w
                                                            FStar_Extraction_ML_Syntax.ml_bool_ty
                                                           in
                                                        ((Some w2), f_w))
                                                in
                                             (match uu____5867 with
                                              | (when_opt1,f_when) ->
                                                  let uu____5910 =
                                                    term_as_mlexpr env
                                                      branch1
                                                     in
                                                  (match uu____5910 with
                                                   | (mlbranch,f_branch,t_branch)
                                                       ->
                                                       let uu____5929 =
                                                         FStar_All.pipe_right
                                                           p
                                                           (FStar_List.map
                                                              (fun uu____5966
                                                                  ->
                                                                 match uu____5966
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
                                                         uu____5929))))) true)
                           in
                        match uu____5756 with
                        | (pat_t_compat,mlbranches) ->
                            let mlbranches1 = FStar_List.flatten mlbranches
                               in
                            let e1 =
                              if pat_t_compat
                              then e
                              else
                                (FStar_Extraction_ML_UEnv.debug g
                                   (fun uu____6052  ->
                                      let uu____6053 =
                                        FStar_Extraction_ML_Code.string_of_mlexpr
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          e
                                         in
                                      let uu____6054 =
                                        FStar_Extraction_ML_Code.string_of_mlty
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          t_e
                                         in
                                      FStar_Util.print2
                                        "Coercing scrutinee %s from type %s because pattern type is incompatible\n"
                                        uu____6053 uu____6054);
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty t_e)
                                   (FStar_Extraction_ML_Syntax.MLE_Coerce
                                      (e, t_e,
                                        FStar_Extraction_ML_Syntax.MLTY_Top)))
                               in
                            (match mlbranches1 with
                             | [] ->
                                 let uu____6067 =
                                   let uu____6071 =
                                     let uu____6079 =
                                       FStar_Syntax_Syntax.lid_as_fv
                                         FStar_Syntax_Const.failwith_lid
                                         FStar_Syntax_Syntax.Delta_constant
                                         None
                                        in
                                     FStar_Extraction_ML_UEnv.lookup_fv g
                                       uu____6079
                                      in
                                   FStar_All.pipe_left FStar_Util.right
                                     uu____6071
                                    in
                                 (match uu____6067 with
                                  | (fw,uu____6099,uu____6100) ->
                                      let uu____6101 =
                                        let uu____6102 =
                                          let uu____6103 =
                                            let uu____6107 =
                                              let uu____6109 =
                                                FStar_All.pipe_left
                                                  (FStar_Extraction_ML_Syntax.with_ty
                                                     FStar_Extraction_ML_Syntax.ml_string_ty)
                                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                                     (FStar_Extraction_ML_Syntax.MLC_String
                                                        "unreachable"))
                                                 in
                                              [uu____6109]  in
                                            (fw, uu____6107)  in
                                          FStar_Extraction_ML_Syntax.MLE_App
                                            uu____6103
                                           in
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             FStar_Extraction_ML_Syntax.ml_unit_ty)
                                          uu____6102
                                         in
                                      (uu____6101,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        FStar_Extraction_ML_Syntax.ml_unit_ty))
                             | (uu____6111,uu____6112,(uu____6113,f_first,t_first))::rest
                                 ->
                                 let uu____6145 =
                                   FStar_List.fold_left
                                     (fun uu____6161  ->
                                        fun uu____6162  ->
                                          match (uu____6161, uu____6162) with
                                          | ((topt,f),(uu____6192,uu____6193,
                                                       (uu____6194,f_branch,t_branch)))
                                              ->
                                              let f1 =
                                                FStar_Extraction_ML_Util.join
                                                  top.FStar_Syntax_Syntax.pos
                                                  f f_branch
                                                 in
                                              let topt1 =
                                                match topt with
                                                | None  -> None
                                                | Some t1 ->
                                                    let uu____6225 =
                                                      type_leq g t1 t_branch
                                                       in
                                                    if uu____6225
                                                    then Some t_branch
                                                    else
                                                      (let uu____6228 =
                                                         type_leq g t_branch
                                                           t1
                                                          in
                                                       if uu____6228
                                                       then Some t1
                                                       else None)
                                                 in
                                              (topt1, f1))
                                     ((Some t_first), f_first) rest
                                    in
                                 (match uu____6145 with
                                  | (topt,f_match) ->
                                      let mlbranches2 =
                                        FStar_All.pipe_right mlbranches1
                                          (FStar_List.map
                                             (fun uu____6274  ->
                                                match uu____6274 with
                                                | (p,(wopt,uu____6290),
                                                   (b1,uu____6292,t1)) ->
                                                    let b2 =
                                                      match topt with
                                                      | None  ->
                                                          FStar_Extraction_ML_Syntax.apply_obj_repr
                                                            b1 t1
                                                      | Some uu____6303 -> b1
                                                       in
                                                    (p, wopt, b2)))
                                         in
                                      let t_match =
                                        match topt with
                                        | None  ->
                                            FStar_Extraction_ML_Syntax.MLTY_Top
                                        | Some t1 -> t1  in
                                      let uu____6307 =
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             t_match)
                                          (FStar_Extraction_ML_Syntax.MLE_Match
                                             (e1, mlbranches2))
                                         in
                                      (uu____6307, f_match, t_match)))))))

let fresh : Prims.string -> (Prims.string * Prims.int) =
  let c = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun x  ->
    FStar_Util.incr c; (let uu____6325 = FStar_ST.read c  in (x, uu____6325))
  
let ind_discriminator_body :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlmodule1
  =
  fun env  ->
    fun discName  ->
      fun constrName  ->
        let uu____6337 =
          FStar_TypeChecker_Env.lookup_lid env.FStar_Extraction_ML_UEnv.tcenv
            discName
           in
        match uu____6337 with
        | (uu____6340,fstar_disc_type) ->
            let wildcards =
              let uu____6348 =
                let uu____6349 = FStar_Syntax_Subst.compress fstar_disc_type
                   in
                uu____6349.FStar_Syntax_Syntax.n  in
              match uu____6348 with
              | FStar_Syntax_Syntax.Tm_arrow (binders,uu____6358) ->
                  let uu____6369 =
                    FStar_All.pipe_right binders
                      (FStar_List.filter
                         (fun uu___138_6384  ->
                            match uu___138_6384 with
                            | (uu____6388,Some (FStar_Syntax_Syntax.Implicit
                               uu____6389)) -> true
                            | uu____6391 -> false))
                     in
                  FStar_All.pipe_right uu____6369
                    (FStar_List.map
                       (fun uu____6411  ->
                          let uu____6415 = fresh "_"  in
                          (uu____6415, FStar_Extraction_ML_Syntax.MLTY_Top)))
              | uu____6420 -> failwith "Discriminator must be a function"  in
            let mlid = fresh "_discr_"  in
            let targ = FStar_Extraction_ML_Syntax.MLTY_Top  in
            let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top  in
            let discrBody =
              let uu____6432 =
                let uu____6433 =
                  let uu____6439 =
                    let uu____6440 =
                      let uu____6441 =
                        let uu____6449 =
                          let uu____6450 =
                            let uu____6451 =
                              let uu____6452 =
                                FStar_Extraction_ML_Syntax.idsym mlid  in
                              ([], uu____6452)  in
                            FStar_Extraction_ML_Syntax.MLE_Name uu____6451
                             in
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty targ)
                            uu____6450
                           in
                        let uu____6454 =
                          let uu____6460 =
                            let uu____6465 =
                              let uu____6466 =
                                let uu____6470 =
                                  FStar_Extraction_ML_Syntax.mlpath_of_lident
                                    constrName
                                   in
                                (uu____6470,
                                  [FStar_Extraction_ML_Syntax.MLP_Wild])
                                 in
                              FStar_Extraction_ML_Syntax.MLP_CTor uu____6466
                               in
                            let uu____6472 =
                              FStar_All.pipe_left
                                (FStar_Extraction_ML_Syntax.with_ty
                                   FStar_Extraction_ML_Syntax.ml_bool_ty)
                                (FStar_Extraction_ML_Syntax.MLE_Const
                                   (FStar_Extraction_ML_Syntax.MLC_Bool true))
                               in
                            (uu____6465, None, uu____6472)  in
                          let uu____6474 =
                            let uu____6480 =
                              let uu____6485 =
                                FStar_All.pipe_left
                                  (FStar_Extraction_ML_Syntax.with_ty
                                     FStar_Extraction_ML_Syntax.ml_bool_ty)
                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                     (FStar_Extraction_ML_Syntax.MLC_Bool
                                        false))
                                 in
                              (FStar_Extraction_ML_Syntax.MLP_Wild, None,
                                uu____6485)
                               in
                            [uu____6480]  in
                          uu____6460 :: uu____6474  in
                        (uu____6449, uu____6454)  in
                      FStar_Extraction_ML_Syntax.MLE_Match uu____6441  in
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.ml_bool_ty) uu____6440
                     in
                  ((FStar_List.append wildcards [(mlid, targ)]), uu____6439)
                   in
                FStar_Extraction_ML_Syntax.MLE_Fun uu____6433  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty disc_ty) uu____6432
               in
            let uu____6523 =
              let uu____6524 =
                let uu____6526 =
                  let uu____6527 =
                    FStar_Extraction_ML_UEnv.convIdent
                      discName.FStar_Ident.ident
                     in
                  {
                    FStar_Extraction_ML_Syntax.mllb_name = uu____6527;
                    FStar_Extraction_ML_Syntax.mllb_tysc = None;
                    FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                    FStar_Extraction_ML_Syntax.mllb_def = discrBody;
                    FStar_Extraction_ML_Syntax.print_typ = false
                  }  in
                [uu____6526]  in
              (FStar_Extraction_ML_Syntax.NonRec, [], uu____6524)  in
            FStar_Extraction_ML_Syntax.MLM_Let uu____6523
  