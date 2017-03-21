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
    | Some l -> l
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
      let uu____261 =
        let uu____262 = FStar_Syntax_Subst.compress t  in
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
          is_arity env (FStar_Syntax_Util.comp_result c)
      | FStar_Syntax_Syntax.Tm_fvar uu____285 ->
          let t =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Normalize.AllowUnboundUniverses;
              FStar_TypeChecker_Normalize.EraseUniverses;
              FStar_TypeChecker_Normalize.UnfoldUntil
                FStar_Syntax_Syntax.Delta_constant]
              env.FStar_Extraction_ML_UEnv.tcenv t
             in
          let uu____287 =
            let uu____288 = FStar_Syntax_Subst.compress t  in
            uu____288.FStar_Syntax_Syntax.n  in
          (match uu____287 with
           | FStar_Syntax_Syntax.Tm_fvar uu____291 -> false
           | uu____292 -> is_arity env t)
      | FStar_Syntax_Syntax.Tm_app uu____293 ->
          let uu____303 = FStar_Syntax_Util.head_and_args t  in
          (match uu____303 with | (head,uu____314) -> is_arity env head)
      | FStar_Syntax_Syntax.Tm_uinst (head,uu____330) -> is_arity env head
      | FStar_Syntax_Syntax.Tm_refine (x,uu____336) ->
          is_arity env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_abs (_,body,_)|FStar_Syntax_Syntax.Tm_let
        (_,body) -> is_arity env body
      | FStar_Syntax_Syntax.Tm_match (uu____365,branches) ->
          (match branches with
           | (uu____393,uu____394,e)::uu____396 -> is_arity env e
           | uu____432 -> false)
  
let rec is_type_aux :
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let t = FStar_Syntax_Subst.compress t  in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed _|FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____452 =
            let uu____453 = FStar_Syntax_Print.tag_of_term t  in
            FStar_Util.format1 "Impossible: %s" uu____453  in
          failwith uu____452
      | FStar_Syntax_Syntax.Tm_constant uu____454 -> false
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
          if uu____460
          then true
          else
            (let uu____466 =
               FStar_TypeChecker_Env.lookup_lid
                 env.FStar_Extraction_ML_UEnv.tcenv
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             match uu____466 with | (uu____473,t) -> is_arity env t)
      | FStar_Syntax_Syntax.Tm_uvar (_,t)
        |FStar_Syntax_Syntax.Tm_bvar
         { FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _;
           FStar_Syntax_Syntax.sort = t;_}|FStar_Syntax_Syntax.Tm_name
         { FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _;
           FStar_Syntax_Syntax.sort = t;_}
          -> is_arity env t
      | FStar_Syntax_Syntax.Tm_ascribed (t,uu____494,uu____495) ->
          is_type_aux env t
      | FStar_Syntax_Syntax.Tm_uinst (t,uu____515) -> is_type_aux env t
      | FStar_Syntax_Syntax.Tm_abs (uu____520,body,uu____522) ->
          is_type_aux env body
      | FStar_Syntax_Syntax.Tm_let (uu____545,body) -> is_type_aux env body
      | FStar_Syntax_Syntax.Tm_match (uu____557,branches) ->
          (match branches with
           | (uu____585,uu____586,e)::uu____588 -> is_type_aux env e
           | uu____624 -> failwith "Empty branches")
      | FStar_Syntax_Syntax.Tm_meta (t,uu____637) -> is_type_aux env t
      | FStar_Syntax_Syntax.Tm_app (head,uu____643) -> is_type_aux env head
  
let is_type :
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let b = is_type_aux env t  in
      FStar_Extraction_ML_UEnv.debug env
        (fun uu____666  ->
           if b
           then
             let uu____667 = FStar_Syntax_Print.term_to_string t  in
             let uu____668 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.print2 "is_type %s (%s)\n" uu____667 uu____668
           else
             (let uu____670 = FStar_Syntax_Print.term_to_string t  in
              let uu____671 = FStar_Syntax_Print.tag_of_term t  in
              FStar_Util.print2 "not a type %s (%s)\n" uu____670 uu____671));
      b
  
let is_type_binder env x =
  is_arity env (Prims.fst x).FStar_Syntax_Syntax.sort 
let is_constructor : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____691 =
      let uu____692 = FStar_Syntax_Subst.compress t  in
      uu____692.FStar_Syntax_Syntax.n  in
    match uu____691 with
    | FStar_Syntax_Syntax.Tm_fvar
      { FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _;
        FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor );_}
      |FStar_Syntax_Syntax.Tm_fvar
      { FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _;
        FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor
          _);_}
        -> true
    | uu____700 -> false
  
let rec is_fstar_value : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____704 =
      let uu____705 = FStar_Syntax_Subst.compress t  in
      uu____705.FStar_Syntax_Syntax.n  in
    match uu____704 with
    | FStar_Syntax_Syntax.Tm_constant _
      |FStar_Syntax_Syntax.Tm_bvar _
       |FStar_Syntax_Syntax.Tm_fvar _|FStar_Syntax_Syntax.Tm_abs _ -> true
    | FStar_Syntax_Syntax.Tm_app (head,args) ->
        let uu____728 = is_constructor head  in
        if uu____728
        then
          FStar_All.pipe_right args
            (FStar_List.for_all
               (fun uu____736  ->
                  match uu____736 with | (te,uu____740) -> is_fstar_value te))
        else false
    | FStar_Syntax_Syntax.Tm_meta (t,_)|FStar_Syntax_Syntax.Tm_ascribed
      (t,_,_) -> is_fstar_value t
    | uu____761 -> false
  
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
    | FStar_Extraction_ML_Syntax.MLE_Record (uu____774,fields) ->
        FStar_Util.for_all
          (fun uu____786  ->
             match uu____786 with | (uu____789,e) -> is_ml_value e) fields
    | uu____791 -> false
  
let normalize_abs : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t0  ->
    let rec aux bs t copt =
      let t = FStar_Syntax_Subst.compress t  in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_abs (bs',body,copt) ->
          aux (FStar_List.append bs bs') body copt
      | uu____851 ->
          let e' = FStar_Syntax_Util.unascribe t  in
          let uu____853 = FStar_Syntax_Util.is_fun e'  in
          if uu____853
          then aux bs e' copt
          else FStar_Syntax_Util.abs bs e' copt
       in
    aux [] t0 None
  
let unit_binder : FStar_Syntax_Syntax.binder =
  let uu____862 =
    FStar_Syntax_Syntax.new_bv None FStar_TypeChecker_Common.t_unit  in
  FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____862 
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
      (let uu____906 = FStar_List.hd l  in
       match uu____906 with
       | (p1,w1,e1) ->
           let uu____925 =
             let uu____930 = FStar_List.tl l  in FStar_List.hd uu____930  in
           (match uu____925 with
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
                 | uu____969 -> def)))
  
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
            let uu____1012 = erasable g f ty  in
            if uu____1012
            then
              let uu____1013 =
                type_leq g ty FStar_Extraction_ML_Syntax.ml_unit_ty  in
              (if uu____1013
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
          let uu____1029 = (type_leq_c g (Some e) ty) expect  in
          match uu____1029 with
          | (true ,Some e') -> e'
          | uu____1035 ->
              (FStar_Extraction_ML_UEnv.debug g
                 (fun uu____1040  ->
                    let uu____1041 =
                      FStar_Extraction_ML_Code.string_of_mlexpr
                        g.FStar_Extraction_ML_UEnv.currentModule e
                       in
                    let uu____1042 =
                      FStar_Extraction_ML_Code.string_of_mlty
                        g.FStar_Extraction_ML_UEnv.currentModule ty
                       in
                    let uu____1043 =
                      FStar_Extraction_ML_Code.string_of_mlty
                        g.FStar_Extraction_ML_UEnv.currentModule expect
                       in
                    FStar_Util.print3
                      "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n"
                      uu____1041 uu____1042 uu____1043);
               FStar_All.pipe_left
                 (FStar_Extraction_ML_Syntax.with_ty expect)
                 (FStar_Extraction_ML_Syntax.MLE_Coerce (e, ty, expect)))
  
let bv_as_mlty :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlty
  =
  fun g  ->
    fun bv  ->
      let uu____1050 = FStar_Extraction_ML_UEnv.lookup_bv g bv  in
      match uu____1050 with
      | FStar_Util.Inl (uu____1051,t) -> t
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
        (fun t  ->
           match t with
           | FStar_Extraction_ML_Syntax.MLTY_Top  -> true
           | FStar_Extraction_ML_Syntax.MLTY_Named uu____1095 ->
               let uu____1099 = FStar_Extraction_ML_Util.udelta_unfold g t
                  in
               (match uu____1099 with
                | None  -> false
                | Some t ->
                    (let rec is_top_ty t =
                       match t with
                       | FStar_Extraction_ML_Syntax.MLTY_Top  -> true
                       | FStar_Extraction_ML_Syntax.MLTY_Named uu____1106 ->
                           let uu____1110 =
                             FStar_Extraction_ML_Util.udelta_unfold g t  in
                           (match uu____1110 with
                            | None  -> false
                            | Some t -> is_top_ty t)
                       | uu____1113 -> false  in
                     is_top_ty) t)
           | uu____1114 -> false) mlt
         in
      if uu____1093
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
          let uu____1122 =
            let uu____1123 = FStar_Syntax_Print.term_to_string t  in
            FStar_Util.format1 "Impossible: Unexpected term %s" uu____1123
             in
          failwith uu____1122
      | FStar_Syntax_Syntax.Tm_constant uu____1124 ->
          FStar_Extraction_ML_UEnv.unknownType
      | FStar_Syntax_Syntax.Tm_uvar uu____1125 ->
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
          let uu____1183 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____1183 with
           | (bs,c) ->
               let uu____1188 = binders_as_ml_binders env bs  in
               (match uu____1188 with
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
                      let uu____1205 =
                        FStar_All.pipe_right
                          ed.FStar_Syntax_Syntax.qualifiers
                          (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                         in
                      if uu____1205
                      then
                        let t =
                          FStar_TypeChecker_Env.reify_comp
                            env.FStar_Extraction_ML_UEnv.tcenv c
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
                    let uu____1211 =
                      FStar_List.fold_right
                        (fun uu____1218  ->
                           fun uu____1219  ->
                             match (uu____1218, uu____1219) with
                             | ((uu____1230,t),(tag,t')) ->
                                 (FStar_Extraction_ML_Syntax.E_PURE,
                                   (FStar_Extraction_ML_Syntax.MLTY_Fun
                                      (t, tag, t')))) mlbs (erase, t_ret)
                       in
                    (match uu____1211 with | (uu____1238,t) -> t)))
      | FStar_Syntax_Syntax.Tm_app (head,args) ->
          let res =
            let uu____1257 =
              let uu____1258 = FStar_Syntax_Util.un_uinst head  in
              uu____1258.FStar_Syntax_Syntax.n  in
            match uu____1257 with
            | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
            | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv args
            | FStar_Syntax_Syntax.Tm_app (head,args') ->
                let uu____1279 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app
                       (head, (FStar_List.append args' args))) None
                    t.FStar_Syntax_Syntax.pos
                   in
                term_as_mlty' env uu____1279
            | uu____1295 -> FStar_Extraction_ML_UEnv.unknownType  in
          res
      | FStar_Syntax_Syntax.Tm_abs (bs,ty,uu____1298) ->
          let uu____1321 = FStar_Syntax_Subst.open_term bs ty  in
          (match uu____1321 with
           | (bs,ty) ->
               let uu____1326 = binders_as_ml_binders env bs  in
               (match uu____1326 with | (bts,env) -> term_as_mlty' env ty))
      | FStar_Syntax_Syntax.Tm_type _
        |FStar_Syntax_Syntax.Tm_let _|FStar_Syntax_Syntax.Tm_match _ ->
          FStar_Extraction_ML_UEnv.unknownType

and arg_as_mlty :
  FStar_Extraction_ML_UEnv.env ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual) ->
      FStar_Extraction_ML_Syntax.mlty
  =
  fun g  ->
    fun uu____1344  ->
      match uu____1344 with
      | (a,uu____1348) ->
          let uu____1349 = is_type g a  in
          if uu____1349
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
        let uu____1354 =
          FStar_Syntax_Util.arrow_formals
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.ty
           in
        match uu____1354 with
        | (formals,t) ->
            let mlargs = FStar_List.map (arg_as_mlty g) args  in
            let mlargs =
              let n_args = FStar_List.length args  in
              if (FStar_List.length formals) > n_args
              then
                let uu____1398 = FStar_Util.first_N n_args formals  in
                match uu____1398 with
                | (uu____1412,rest) ->
                    let uu____1426 =
                      FStar_List.map
                        (fun uu____1430  ->
                           FStar_Extraction_ML_UEnv.erasedContent) rest
                       in
                    FStar_List.append mlargs uu____1426
              else mlargs  in
            let nm =
              let uu____1435 =
                FStar_Extraction_ML_UEnv.maybe_mangle_type_projector g fv  in
              match uu____1435 with
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
      let uu____1450 =
        FStar_All.pipe_right bs
          (FStar_List.fold_left
             (fun uu____1474  ->
                fun b  ->
                  match uu____1474 with
                  | (ml_bs,env) ->
                      let uu____1504 = is_type_binder g b  in
                      if uu____1504
                      then
                        let b = Prims.fst b  in
                        let env =
                          FStar_Extraction_ML_UEnv.extend_ty env b
                            (Some FStar_Extraction_ML_Syntax.MLTY_Top)
                           in
                        let ml_b =
                          let uu____1519 =
                            FStar_Extraction_ML_UEnv.bv_as_ml_termvar b  in
                          (uu____1519, FStar_Extraction_ML_Syntax.ml_unit_ty)
                           in
                        ((ml_b :: ml_bs), env)
                      else
                        (let b = Prims.fst b  in
                         let t = term_as_mlty env b.FStar_Syntax_Syntax.sort
                            in
                         let uu____1536 =
                           FStar_Extraction_ML_UEnv.extend_bv env b ([], t)
                             false false false
                            in
                         match uu____1536 with
                         | (env,b) ->
                             let ml_b =
                               let uu____1554 =
                                 FStar_Extraction_ML_UEnv.removeTick b  in
                               (uu____1554, t)  in
                             ((ml_b :: ml_bs), env))) ([], g))
         in
      match uu____1450 with | (ml_bs,env) -> ((FStar_List.rev ml_bs), env)

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
      | (FStar_Extraction_ML_Syntax.MLE_Seq es1,uu____1614) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (FStar_List.append es1 [e2])
      | (uu____1616,FStar_Extraction_ML_Syntax.MLE_Seq es2) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (e1 :: es2)
      | uu____1619 -> FStar_Extraction_ML_Syntax.MLE_Seq [e1; e2]
  
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
                    | uu____1641 when
                        (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
                          =
                          FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr
                        -> body.FStar_Extraction_ML_Syntax.expr
                    | uu____1642 ->
                        mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def
                          body)
             | uu____1643 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body))
        | uu____1645 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body)
  
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
           | uu____1659 ->
               (match q with
                | Some (FStar_Syntax_Syntax.Record_ctor (ty,fns)) ->
                    let path =
                      FStar_List.map FStar_Ident.text_of_id ty.FStar_Ident.ns
                       in
                    let fs = record_fields fns pats  in
                    FStar_Extraction_ML_Syntax.MLP_Record (path, fs)
                | uu____1675 -> p))
      | uu____1677 -> p
  
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
                       (fun uu____1716  ->
                          let uu____1717 =
                            FStar_Extraction_ML_Code.string_of_mlty
                              g.FStar_Extraction_ML_UEnv.currentModule t'
                             in
                          let uu____1718 =
                            FStar_Extraction_ML_Code.string_of_mlty
                              g.FStar_Extraction_ML_UEnv.currentModule t
                             in
                          FStar_Util.print2
                            "Expected pattern type %s; got pattern type %s\n"
                            uu____1717 uu____1718)
                   else ();
                   ok)
               in
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_disj uu____1727 ->
                failwith "Impossible: Nested disjunctive pattern"
            | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int
                (c,None )) ->
                let i = FStar_Const.Const_int (c, None)  in
                let x = FStar_Extraction_ML_Syntax.gensym ()  in
                let when_clause =
                  let uu____1752 =
                    let uu____1753 =
                      let uu____1757 =
                        let uu____1759 =
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty
                               FStar_Extraction_ML_Syntax.ml_int_ty)
                            (FStar_Extraction_ML_Syntax.MLE_Var x)
                           in
                        let uu____1760 =
                          let uu____1762 =
                            let uu____1763 =
                              let uu____1764 =
                                FStar_Extraction_ML_Util.mlconst_of_const'
                                  p.FStar_Syntax_Syntax.p i
                                 in
                              FStar_All.pipe_left
                                (fun _0_30  ->
                                   FStar_Extraction_ML_Syntax.MLE_Const _0_30)
                                uu____1764
                               in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.ml_int_ty)
                              uu____1763
                             in
                          [uu____1762]  in
                        uu____1759 :: uu____1760  in
                      (FStar_Extraction_ML_Util.prims_op_equality,
                        uu____1757)
                       in
                    FStar_Extraction_ML_Syntax.MLE_App uu____1753  in
                  FStar_All.pipe_left
                    (FStar_Extraction_ML_Syntax.with_ty
                       FStar_Extraction_ML_Syntax.ml_bool_ty) uu____1752
                   in
                let uu____1766 = ok FStar_Extraction_ML_Syntax.ml_int_ty  in
                (g,
                  (Some
                     ((FStar_Extraction_ML_Syntax.MLP_Var x), [when_clause])),
                  uu____1766)
            | FStar_Syntax_Syntax.Pat_constant s ->
                let t =
                  FStar_TypeChecker_TcTerm.tc_constant FStar_Range.dummyRange
                    s
                   in
                let mlty = term_as_mlty g t  in
                let uu____1778 =
                  let uu____1783 =
                    let uu____1787 =
                      let uu____1788 =
                        FStar_Extraction_ML_Util.mlconst_of_const'
                          p.FStar_Syntax_Syntax.p s
                         in
                      FStar_Extraction_ML_Syntax.MLP_Const uu____1788  in
                    (uu____1787, [])  in
                  Some uu____1783  in
                let uu____1793 = ok mlty  in (g, uu____1778, uu____1793)
            | FStar_Syntax_Syntax.Pat_var x|FStar_Syntax_Syntax.Pat_wild x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort  in
                let uu____1800 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp
                   in
                (match uu____1800 with
                 | (g,x) ->
                     let uu____1813 = ok mlty  in
                     (g,
                       (if imp
                        then None
                        else
                          Some ((FStar_Extraction_ML_Syntax.MLP_Var x), [])),
                       uu____1813))
            | FStar_Syntax_Syntax.Pat_wild x when disjunctive_pat ->
                (g, (Some (FStar_Extraction_ML_Syntax.MLP_Wild, [])), true)
            | FStar_Syntax_Syntax.Pat_dot_term uu____1839 -> (g, None, true)
            | FStar_Syntax_Syntax.Pat_cons (f,pats) ->
                let uu____1863 =
                  let uu____1866 = FStar_Extraction_ML_UEnv.lookup_fv g f  in
                  match uu____1866 with
                  | FStar_Util.Inr
                      (uu____1869,{
                                    FStar_Extraction_ML_Syntax.expr =
                                      FStar_Extraction_ML_Syntax.MLE_Name n;
                                    FStar_Extraction_ML_Syntax.mlty =
                                      uu____1871;
                                    FStar_Extraction_ML_Syntax.loc =
                                      uu____1872;_},ttys,uu____1874)
                      -> (n, ttys)
                  | uu____1881 -> failwith "Expected a constructor"  in
                (match uu____1863 with
                 | (d,tys) ->
                     let nTyVars = FStar_List.length (Prims.fst tys)  in
                     let uu____1895 = FStar_Util.first_N nTyVars pats  in
                     (match uu____1895 with
                      | (tysVarPats,restPats) ->
                          let f_ty_opt =
                            try
                              let mlty_args =
                                FStar_All.pipe_right tysVarPats
                                  (FStar_List.map
                                     (fun uu____1969  ->
                                        match uu____1969 with
                                        | (p,uu____1975) ->
                                            (match p.FStar_Syntax_Syntax.v
                                             with
                                             | FStar_Syntax_Syntax.Pat_dot_term
                                                 (uu____1980,t) ->
                                                 term_as_mlty g t
                                             | uu____1986 ->
                                                 (FStar_Extraction_ML_UEnv.debug
                                                    g
                                                    (fun uu____1988  ->
                                                       let uu____1989 =
                                                         FStar_Syntax_Print.pat_to_string
                                                           p
                                                          in
                                                       FStar_Util.print1
                                                         "Pattern %s is not extractable"
                                                         uu____1989);
                                                  Prims.raise Un_extractable))))
                                 in
                              let f_ty =
                                FStar_Extraction_ML_Util.subst tys mlty_args
                                 in
                              let uu____1991 =
                                FStar_Extraction_ML_Util.uncurry_mlty_fun
                                  f_ty
                                 in
                              Some uu____1991
                            with | Un_extractable  -> None  in
                          let uu____2006 =
                            FStar_Util.fold_map
                              (fun g  ->
                                 fun uu____2021  ->
                                   match uu____2021 with
                                   | (p,imp) ->
                                       let uu____2032 =
                                         extract_one_pat disjunctive_pat true
                                           g p None
                                          in
                                       (match uu____2032 with
                                        | (g,p,uu____2048) -> (g, p))) g
                              tysVarPats
                             in
                          (match uu____2006 with
                           | (g,tyMLPats) ->
                               let uu____2080 =
                                 FStar_Util.fold_map
                                   (fun uu____2106  ->
                                      fun uu____2107  ->
                                        match (uu____2106, uu____2107) with
                                        | ((g,f_ty_opt),(p,imp)) ->
                                            let uu____2156 =
                                              match f_ty_opt with
                                              | Some (hd::rest,res) ->
                                                  ((Some (rest, res)),
                                                    (Some hd))
                                              | uu____2188 -> (None, None)
                                               in
                                            (match uu____2156 with
                                             | (f_ty_opt,expected_ty) ->
                                                 let uu____2225 =
                                                   extract_one_pat
                                                     disjunctive_pat false g
                                                     p expected_ty
                                                    in
                                                 (match uu____2225 with
                                                  | (g,p,uu____2247) ->
                                                      ((g, f_ty_opt), p))))
                                   (g, f_ty_opt) restPats
                                  in
                               (match uu____2080 with
                                | ((g,f_ty_opt),restMLPats) ->
                                    let uu____2308 =
                                      let uu____2314 =
                                        FStar_All.pipe_right
                                          (FStar_List.append tyMLPats
                                             restMLPats)
                                          (FStar_List.collect
                                             (fun uu___137_2339  ->
                                                match uu___137_2339 with
                                                | Some x -> [x]
                                                | uu____2361 -> []))
                                         in
                                      FStar_All.pipe_right uu____2314
                                        FStar_List.split
                                       in
                                    (match uu____2308 with
                                     | (mlPats,when_clauses) ->
                                         let pat_ty_compat =
                                           match f_ty_opt with
                                           | Some ([],t) -> ok t
                                           | uu____2400 -> false  in
                                         let uu____2405 =
                                           let uu____2410 =
                                             let uu____2414 =
                                               resugar_pat
                                                 f.FStar_Syntax_Syntax.fv_qual
                                                 (FStar_Extraction_ML_Syntax.MLP_CTor
                                                    (d, mlPats))
                                                in
                                             let uu____2416 =
                                               FStar_All.pipe_right
                                                 when_clauses
                                                 FStar_List.flatten
                                                in
                                             (uu____2414, uu____2416)  in
                                           Some uu____2410  in
                                         (g, uu____2405, pat_ty_compat))))))
  
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
          let uu____2477 = extract_one_pat disj false g p expected_t  in
          match uu____2477 with
          | (g,Some (x,v),b) -> (g, (x, v), b)
          | uu____2508 -> failwith "Impossible: Unable to translate pattern"
           in
        let mk_when_clause whens =
          match whens with
          | [] -> None
          | hd::tl ->
              let uu____2533 =
                FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd tl
                 in
              Some uu____2533
           in
        match p.FStar_Syntax_Syntax.v with
        | FStar_Syntax_Syntax.Pat_disj [] ->
            failwith "Impossible: Empty disjunctive pattern"
        | FStar_Syntax_Syntax.Pat_disj (p::pats) ->
            let uu____2559 = extract_one_pat true g p (Some expected_t)  in
            (match uu____2559 with
             | (g,p,b) ->
                 let uu____2582 =
                   FStar_Util.fold_map
                     (fun b  ->
                        fun p  ->
                          let uu____2594 =
                            extract_one_pat true g p (Some expected_t)  in
                          match uu____2594 with
                          | (uu____2606,p,b') -> ((b && b'), p)) b pats
                    in
                 (match uu____2582 with
                  | (b,ps) ->
                      let ps = p :: ps  in
                      let uu____2643 =
                        FStar_All.pipe_right ps
                          (FStar_List.partition
                             (fun uu___138_2671  ->
                                match uu___138_2671 with
                                | (uu____2675,uu____2676::uu____2677) -> true
                                | uu____2680 -> false))
                         in
                      (match uu____2643 with
                       | (ps_when,rest) ->
                           let ps =
                             FStar_All.pipe_right ps_when
                               (FStar_List.map
                                  (fun uu____2728  ->
                                     match uu____2728 with
                                     | (x,whens) ->
                                         let uu____2739 =
                                           mk_when_clause whens  in
                                         (x, uu____2739)))
                              in
                           let res =
                             match rest with
                             | [] -> (g, ps, b)
                             | rest ->
                                 let uu____2769 =
                                   let uu____2774 =
                                     let uu____2778 =
                                       let uu____2779 =
                                         FStar_List.map Prims.fst rest  in
                                       FStar_Extraction_ML_Syntax.MLP_Branch
                                         uu____2779
                                        in
                                     (uu____2778, None)  in
                                   uu____2774 :: ps  in
                                 (g, uu____2769, b)
                              in
                           res)))
        | uu____2793 ->
            let uu____2794 = extract_one_pat false g p (Some expected_t)  in
            (match uu____2794 with
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
            | FStar_Extraction_ML_Syntax.MLTY_Fun (t0,uu____2876,t1) ->
                let x = FStar_Extraction_ML_Syntax.gensym ()  in
                let uu____2879 =
                  let uu____2885 =
                    let uu____2890 =
                      FStar_All.pipe_left
                        (FStar_Extraction_ML_Syntax.with_ty t0)
                        (FStar_Extraction_ML_Syntax.MLE_Var x)
                       in
                    ((x, t0), uu____2890)  in
                  uu____2885 :: more_args  in
                eta_args uu____2879 t1
            | FStar_Extraction_ML_Syntax.MLTY_Named (uu____2897,uu____2898)
                -> ((FStar_List.rev more_args), t)
            | uu____2910 -> failwith "Impossible: Head type is not an arrow"
             in
          let as_record qual e =
            match ((e.FStar_Extraction_ML_Syntax.expr), qual) with
            | (FStar_Extraction_ML_Syntax.MLE_CTor (uu____2928,args),Some
               (FStar_Syntax_Syntax.Record_ctor (tyname,fields))) ->
                let path =
                  FStar_List.map FStar_Ident.text_of_id tyname.FStar_Ident.ns
                   in
                let fields = record_fields fields args  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     e.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_Record (path, fields))
            | uu____2947 -> e  in
          let resugar_and_maybe_eta qual e =
            let uu____2960 = eta_args [] residualType  in
            match uu____2960 with
            | (eargs,tres) ->
                (match eargs with
                 | [] ->
                     let uu____2988 = as_record qual e  in
                     FStar_Extraction_ML_Util.resugar_exp uu____2988
                 | uu____2989 ->
                     let uu____2995 = FStar_List.unzip eargs  in
                     (match uu____2995 with
                      | (binders,eargs) ->
                          (match e.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_CTor (head,args)
                               ->
                               let body =
                                 let uu____3019 =
                                   let uu____3020 =
                                     FStar_All.pipe_left
                                       (FStar_Extraction_ML_Syntax.with_ty
                                          tres)
                                       (FStar_Extraction_ML_Syntax.MLE_CTor
                                          (head,
                                            (FStar_List.append args eargs)))
                                      in
                                   FStar_All.pipe_left (as_record qual)
                                     uu____3020
                                    in
                                 FStar_All.pipe_left
                                   FStar_Extraction_ML_Util.resugar_exp
                                   uu____3019
                                  in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    e.FStar_Extraction_ML_Syntax.mlty)
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    (binders, body))
                           | uu____3025 ->
                               failwith "Impossible: Not a constructor")))
             in
          match ((mlAppExpr.FStar_Extraction_ML_Syntax.expr), qual) with
          | (uu____3027,None ) -> mlAppExpr
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____3030;
                FStar_Extraction_ML_Syntax.loc = uu____3031;_},mle::args),Some
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
                | uu____3049 ->
                    let uu____3051 =
                      let uu____3055 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj
                         in
                      (uu____3055, args)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____3051
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
              let uu____3070 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____3070
          | (FStar_Extraction_ML_Syntax.MLE_Name mlp,Some
             (FStar_Syntax_Syntax.Data_ctor ))
            |(FStar_Extraction_ML_Syntax.MLE_Name mlp,Some
              (FStar_Syntax_Syntax.Record_ctor _)) ->
              let uu____3076 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____3076
          | uu____3078 -> mlAppExpr
  
let maybe_downgrade_eff :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.e_tag ->
      FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.e_tag
  =
  fun g  ->
    fun f  ->
      fun t  ->
        let uu____3091 =
          (f = FStar_Extraction_ML_Syntax.E_GHOST) &&
            (type_leq g t FStar_Extraction_ML_Syntax.ml_unit_ty)
           in
        if uu____3091 then FStar_Extraction_ML_Syntax.E_PURE else f
  
let rec term_as_mlexpr :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag *
        FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun t  ->
      let uu____3132 = term_as_mlexpr' g t  in
      match uu____3132 with
      | (e,tag,ty) ->
          let tag = maybe_downgrade_eff g tag ty  in
          (FStar_Extraction_ML_UEnv.debug g
             (fun u  ->
                let uu____3145 =
                  let uu____3146 = FStar_Syntax_Print.tag_of_term t  in
                  let uu____3147 = FStar_Syntax_Print.term_to_string t  in
                  let uu____3148 =
                    FStar_Extraction_ML_Code.string_of_mlty
                      g.FStar_Extraction_ML_UEnv.currentModule ty
                     in
                  FStar_Util.format4
                    "term_as_mlexpr (%s) :  %s has ML type %s and effect %s\n"
                    uu____3146 uu____3147 uu____3148
                    (FStar_Extraction_ML_Util.eff_to_string tag)
                   in
                FStar_Util.print_string uu____3145);
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
          let uu____3155 = check_term_as_mlexpr' g t f ty  in
          match uu____3155 with
          | (e,t) ->
              let uu____3162 = erase g e t f  in
              (match uu____3162 with | (r,uu____3169,t) -> (r, t))

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
          let uu____3177 = term_as_mlexpr g e0  in
          match uu____3177 with
          | (e,tag,t) ->
              let tag = maybe_downgrade_eff g tag t  in
              if FStar_Extraction_ML_Util.eff_leq tag f
              then
                let uu____3189 = maybe_coerce g e t ty  in (uu____3189, ty)
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
           let uu____3200 =
             let uu____3201 =
               FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos  in
             let uu____3202 = FStar_Syntax_Print.tag_of_term top  in
             let uu____3203 = FStar_Syntax_Print.term_to_string top  in
             FStar_Util.format3 "%s: term_as_mlexpr' (%s) :  %s \n"
               uu____3201 uu____3202 uu____3203
              in
           FStar_Util.print_string uu____3200);
      (let t = FStar_Syntax_Subst.compress top  in
       match t.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_unknown 
         |FStar_Syntax_Syntax.Tm_delayed _
          |FStar_Syntax_Syntax.Tm_uvar _|FStar_Syntax_Syntax.Tm_bvar _ ->
           let uu____3211 =
             let uu____3212 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____3212
              in
           failwith uu____3211
       | FStar_Syntax_Syntax.Tm_type _
         |FStar_Syntax_Syntax.Tm_refine _|FStar_Syntax_Syntax.Tm_arrow _ ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Mutable_alloc ))
           ->
           let uu____3224 = term_as_mlexpr' g t  in
           (match uu____3224 with
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
            | uu____3251 -> failwith "impossible")
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,uu____3260)) ->
           let t = FStar_Syntax_Subst.compress t  in
           (match t.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) when
                FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname ->
                let ed =
                  FStar_TypeChecker_Env.get_effect_decl
                    g.FStar_Extraction_ML_UEnv.tcenv m
                   in
                let uu____3284 =
                  let uu____3285 =
                    FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                     in
                  FStar_All.pipe_right uu____3285 Prims.op_Negation  in
                if uu____3284
                then term_as_mlexpr' g t
                else
                  (let ml_result_ty_1 =
                     term_as_mlty g lb.FStar_Syntax_Syntax.lbtyp  in
                   let uu____3292 =
                     term_as_mlexpr g lb.FStar_Syntax_Syntax.lbdef  in
                   match uu____3292 with
                   | (comp_1,uu____3300,uu____3301) ->
                       let uu____3302 =
                         let k =
                           let uu____3306 =
                             let uu____3310 =
                               let uu____3311 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               FStar_All.pipe_right uu____3311
                                 FStar_Syntax_Syntax.mk_binder
                                in
                             [uu____3310]  in
                           FStar_Syntax_Util.abs uu____3306 body None  in
                         let uu____3317 = term_as_mlexpr g k  in
                         match uu____3317 with
                         | (ml_k,uu____3324,t_k) ->
                             let m_2 =
                               match t_k with
                               | FStar_Extraction_ML_Syntax.MLTY_Fun
                                   (uu____3327,uu____3328,m_2) -> m_2
                               | uu____3330 -> failwith "Impossible"  in
                             (ml_k, m_2)
                          in
                       (match uu____3302 with
                        | (ml_k,ty) ->
                            let bind =
                              let uu____3337 =
                                let uu____3338 =
                                  let uu____3339 =
                                    FStar_Extraction_ML_UEnv.monad_op_name ed
                                      "bind"
                                     in
                                  FStar_All.pipe_right uu____3339 Prims.fst
                                   in
                                FStar_Extraction_ML_Syntax.MLE_Name
                                  uu____3338
                                 in
                              FStar_All.pipe_left
                                (FStar_Extraction_ML_Syntax.with_ty
                                   FStar_Extraction_ML_Syntax.MLTY_Top)
                                uu____3337
                               in
                            let uu____3344 =
                              FStar_All.pipe_left
                                (FStar_Extraction_ML_Syntax.with_ty ty)
                                (FStar_Extraction_ML_Syntax.MLE_App
                                   (bind, [comp_1; ml_k]))
                               in
                            (uu____3344, FStar_Extraction_ML_Syntax.E_IMPURE,
                              ty)))
            | uu____3346 -> term_as_mlexpr' g t)
       | FStar_Syntax_Syntax.Tm_meta (t,_)|FStar_Syntax_Syntax.Tm_uinst (t,_)
           -> term_as_mlexpr' g t
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____3359 =
             FStar_TypeChecker_TcTerm.type_of_tot_term
               g.FStar_Extraction_ML_UEnv.tcenv t
              in
           (match uu____3359 with
            | (uu____3366,ty,uu____3368) ->
                let ml_ty = term_as_mlty g ty  in
                let uu____3370 =
                  let uu____3371 =
                    let uu____3372 =
                      FStar_Extraction_ML_Util.mlconst_of_const'
                        t.FStar_Syntax_Syntax.pos c
                       in
                    FStar_All.pipe_left
                      (fun _0_31  ->
                         FStar_Extraction_ML_Syntax.MLE_Const _0_31)
                      uu____3372
                     in
                  FStar_Extraction_ML_Syntax.with_ty ml_ty uu____3371  in
                (uu____3370, FStar_Extraction_ML_Syntax.E_PURE, ml_ty))
       | FStar_Syntax_Syntax.Tm_name _|FStar_Syntax_Syntax.Tm_fvar _ ->
           let uu____3375 = is_type g t  in
           if uu____3375
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____3380 = FStar_Extraction_ML_UEnv.lookup_term g t  in
              match uu____3380 with
              | (FStar_Util.Inl uu____3387,uu____3388) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | (FStar_Util.Inr (uu____3407,x,mltys,uu____3410),qual) ->
                  (match mltys with
                   | ([],t) when t = FStar_Extraction_ML_Syntax.ml_unit_ty ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t)
                   | ([],t) ->
                       let uu____3435 =
                         maybe_eta_data_and_project_record g qual t x  in
                       (uu____3435, FStar_Extraction_ML_Syntax.E_PURE, t)
                   | uu____3436 -> err_uninst g t mltys t))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,copt) ->
           let uu____3465 = FStar_Syntax_Subst.open_term bs body  in
           (match uu____3465 with
            | (bs,body) ->
                let uu____3473 = binders_as_ml_binders g bs  in
                (match uu____3473 with
                 | (ml_bs,env) ->
                     let uu____3490 = term_as_mlexpr env body  in
                     (match uu____3490 with
                      | (ml_body,f,t) ->
                          let uu____3500 =
                            FStar_List.fold_right
                              (fun uu____3507  ->
                                 fun uu____3508  ->
                                   match (uu____3507, uu____3508) with
                                   | ((uu____3519,targ),(f,t)) ->
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         (FStar_Extraction_ML_Syntax.MLTY_Fun
                                            (targ, f, t)))) ml_bs (f, t)
                             in
                          (match uu____3500 with
                           | (f,tfun) ->
                               let uu____3532 =
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty tfun)
                                   (FStar_Extraction_ML_Syntax.MLE_Fun
                                      (ml_bs, ml_body))
                                  in
                               (uu____3532, f, tfun)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.tk = uu____3536;
              FStar_Syntax_Syntax.pos = uu____3537;
              FStar_Syntax_Syntax.vars = uu____3538;_},t::[])
           ->
           let uu____3561 = term_as_mlexpr' g (Prims.fst t)  in
           (match uu____3561 with
            | (ml,e_tag,mlty) ->
                (ml, FStar_Extraction_ML_Syntax.E_PURE, mlty))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____3573);
              FStar_Syntax_Syntax.tk = uu____3574;
              FStar_Syntax_Syntax.pos = uu____3575;
              FStar_Syntax_Syntax.vars = uu____3576;_},t::[])
           ->
           let uu____3599 = term_as_mlexpr' g (Prims.fst t)  in
           (match uu____3599 with
            | (ml,e_tag,mlty) ->
                (ml, FStar_Extraction_ML_Syntax.E_IMPURE, mlty))
       | FStar_Syntax_Syntax.Tm_app (head,args) ->
           let is_total uu___140_3635 =
             match uu___140_3635 with
             | FStar_Util.Inl l -> FStar_Syntax_Util.is_total_lcomp l
             | FStar_Util.Inr (l,flags) ->
                 (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid)
                   ||
                   (FStar_All.pipe_right flags
                      (FStar_List.existsb
                         (fun uu___139_3653  ->
                            match uu___139_3653 with
                            | FStar_Syntax_Syntax.TOTAL  -> true
                            | uu____3654 -> false)))
              in
           let uu____3655 =
             let uu____3658 =
               let uu____3659 = FStar_Syntax_Subst.compress head  in
               uu____3659.FStar_Syntax_Syntax.n  in
             ((head.FStar_Syntax_Syntax.n), uu____3658)  in
           (match uu____3655 with
            | (FStar_Syntax_Syntax.Tm_uvar uu____3665,uu____3666) ->
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
            | (uu____3676,FStar_Syntax_Syntax.Tm_abs (bs,uu____3678,Some lc))
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
            | uu____3707 ->
                let rec extract_app is_data uu____3735 uu____3736 restArgs =
                  match (uu____3735, uu____3736) with
                  | ((mlhead,mlargs_f),(f,t)) ->
                      (match (restArgs, t) with
                       | ([],uu____3784) ->
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
                                | uu____3798 -> false)
                              in
                           let uu____3799 =
                             if evaluation_order_guaranteed
                             then
                               let uu____3812 =
                                 FStar_All.pipe_right
                                   (FStar_List.rev mlargs_f)
                                   (FStar_List.map Prims.fst)
                                  in
                               ([], uu____3812)
                             else
                               FStar_List.fold_left
                                 (fun uu____3837  ->
                                    fun uu____3838  ->
                                      match (uu____3837, uu____3838) with
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
                                             let uu____3893 =
                                               let uu____3895 =
                                                 FStar_All.pipe_left
                                                   (FStar_Extraction_ML_Syntax.with_ty
                                                      arg.FStar_Extraction_ML_Syntax.mlty)
                                                   (FStar_Extraction_ML_Syntax.MLE_Var
                                                      x)
                                                  in
                                               uu____3895 :: out_args  in
                                             (((x, arg) :: lbs), uu____3893)))
                                 ([], []) mlargs_f
                              in
                           (match uu____3799 with
                            | (lbs,mlargs) ->
                                let app =
                                  let uu____3922 =
                                    FStar_All.pipe_left
                                      (FStar_Extraction_ML_Syntax.with_ty t)
                                      (FStar_Extraction_ML_Syntax.MLE_App
                                         (mlhead, mlargs))
                                     in
                                  FStar_All.pipe_left
                                    (maybe_eta_data_and_project_record g
                                       is_data t) uu____3922
                                   in
                                let l_app =
                                  FStar_List.fold_right
                                    (fun uu____3927  ->
                                       fun out  ->
                                         match uu____3927 with
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
                       | ((arg,uu____3940)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                          (formal_t,f',t)) when is_type g arg ->
                           let uu____3958 =
                             type_leq g formal_t
                               FStar_Extraction_ML_Syntax.ml_unit_ty
                              in
                           if uu____3958
                           then
                             let uu____3962 =
                               let uu____3965 =
                                 FStar_Extraction_ML_Util.join
                                   arg.FStar_Syntax_Syntax.pos f f'
                                  in
                               (uu____3965, t)  in
                             extract_app is_data
                               (mlhead,
                                 ((FStar_Extraction_ML_Syntax.ml_unit,
                                    FStar_Extraction_ML_Syntax.E_PURE) ::
                                 mlargs_f)) uu____3962 rest
                           else
                             (let uu____3972 =
                                let uu____3973 =
                                  FStar_Extraction_ML_Code.string_of_mlexpr
                                    g.FStar_Extraction_ML_UEnv.currentModule
                                    mlhead
                                   in
                                let uu____3974 =
                                  FStar_Syntax_Print.term_to_string arg  in
                                let uu____3975 =
                                  FStar_Syntax_Print.tag_of_term arg  in
                                let uu____3976 =
                                  FStar_Extraction_ML_Code.string_of_mlty
                                    g.FStar_Extraction_ML_UEnv.currentModule
                                    formal_t
                                   in
                                FStar_Util.format4
                                  "Impossible: ill-typed application:\n\thead=%s, arg=%s, tag=%s\n\texpected type unit, got %s"
                                  uu____3973 uu____3974 uu____3975 uu____3976
                                 in
                              failwith uu____3972)
                       | ((e0,uu____3981)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                          (tExpected,f',t)) ->
                           let r = e0.FStar_Syntax_Syntax.pos  in
                           let uu____4000 = term_as_mlexpr g e0  in
                           (match uu____4000 with
                            | (e0,f0,tInferred) ->
                                let e0 =
                                  maybe_coerce g e0 tInferred tExpected  in
                                let uu____4011 =
                                  let uu____4014 =
                                    FStar_Extraction_ML_Util.join_l r
                                      [f; f'; f0]
                                     in
                                  (uu____4014, t)  in
                                extract_app is_data
                                  (mlhead, ((e0, f0) :: mlargs_f)) uu____4011
                                  rest)
                       | uu____4020 ->
                           let uu____4027 =
                             FStar_Extraction_ML_Util.udelta_unfold g t  in
                           (match uu____4027 with
                            | Some t ->
                                extract_app is_data (mlhead, mlargs_f) 
                                  (f, t) restArgs
                            | None  ->
                                err_ill_typed_application g top restArgs t))
                   in
                let extract_app_maybe_projector is_data mlhead uu____4063
                  args =
                  match uu____4063 with
                  | (f,t) ->
                      (match is_data with
                       | Some (FStar_Syntax_Syntax.Record_projector
                           uu____4082) ->
                           let rec remove_implicits args f t =
                             match (args, t) with
                             | ((a0,Some (FStar_Syntax_Syntax.Implicit
                                 uu____4132))::args,FStar_Extraction_ML_Syntax.MLTY_Fun
                                (uu____4134,f',t)) ->
                                 let uu____4159 =
                                   FStar_Extraction_ML_Util.join
                                     a0.FStar_Syntax_Syntax.pos f f'
                                    in
                                 remove_implicits args uu____4159 t
                             | uu____4160 -> (args, f, t)  in
                           let uu____4175 = remove_implicits args f t  in
                           (match uu____4175 with
                            | (args,f,t) ->
                                extract_app is_data (mlhead, []) (f, t) args)
                       | uu____4208 ->
                           extract_app is_data (mlhead, []) (f, t) args)
                   in
                let uu____4215 = is_type g t  in
                if uu____4215
                then
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
                else
                  (let head = FStar_Syntax_Util.un_uinst head  in
                   match head.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_name _
                     |FStar_Syntax_Syntax.Tm_fvar _ ->
                       let uu____4226 =
                         let uu____4233 =
                           FStar_Extraction_ML_UEnv.lookup_term g head  in
                         match uu____4233 with
                         | (FStar_Util.Inr (uu____4243,x1,x2,x3),q) ->
                             ((x1, x2, x3), q)
                         | uu____4268 -> failwith "FIXME Ty"  in
                       (match uu____4226 with
                        | ((head_ml,(vars,t),inst_ok),qual) ->
                            let has_typ_apps =
                              match args with
                              | (a,uu____4297)::uu____4298 -> is_type g a
                              | uu____4312 -> false  in
                            let uu____4318 =
                              match vars with
                              | uu____4335::uu____4336 when
                                  (Prims.op_Negation has_typ_apps) && inst_ok
                                  -> (head_ml, t, args)
                              | uu____4343 ->
                                  let n = FStar_List.length vars  in
                                  if n <= (FStar_List.length args)
                                  then
                                    let uu____4363 =
                                      FStar_Util.first_N n args  in
                                    (match uu____4363 with
                                     | (prefix,rest) ->
                                         let prefixAsMLTypes =
                                           FStar_List.map
                                             (fun uu____4416  ->
                                                match uu____4416 with
                                                | (x,uu____4420) ->
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
                                               let uu___144_4425 = head_ml
                                                  in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (uu___144_4425.FStar_Extraction_ML_Syntax.expr);
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   = t;
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___144_4425.FStar_Extraction_ML_Syntax.loc)
                                               }
                                           | FStar_Extraction_ML_Syntax.MLE_App
                                               (head,{
                                                       FStar_Extraction_ML_Syntax.expr
                                                         =
                                                         FStar_Extraction_ML_Syntax.MLE_Const
                                                         (FStar_Extraction_ML_Syntax.MLC_Unit
                                                         );
                                                       FStar_Extraction_ML_Syntax.mlty
                                                         = uu____4427;
                                                       FStar_Extraction_ML_Syntax.loc
                                                         = uu____4428;_}::[])
                                               ->
                                               FStar_All.pipe_right
                                                 (FStar_Extraction_ML_Syntax.MLE_App
                                                    ((let uu___145_4431 =
                                                        head  in
                                                      {
                                                        FStar_Extraction_ML_Syntax.expr
                                                          =
                                                          (uu___145_4431.FStar_Extraction_ML_Syntax.expr);
                                                        FStar_Extraction_ML_Syntax.mlty
                                                          =
                                                          (FStar_Extraction_ML_Syntax.MLTY_Fun
                                                             (FStar_Extraction_ML_Syntax.ml_unit_ty,
                                                               FStar_Extraction_ML_Syntax.E_PURE,
                                                               t));
                                                        FStar_Extraction_ML_Syntax.loc
                                                          =
                                                          (uu___145_4431.FStar_Extraction_ML_Syntax.loc)
                                                      }),
                                                      [FStar_Extraction_ML_Syntax.ml_unit]))
                                                 (FStar_Extraction_ML_Syntax.with_ty
                                                    t)
                                           | uu____4432 ->
                                               failwith
                                                 "Impossible: Unexpected head term"
                                            in
                                         (head, t, rest))
                                  else err_uninst g head (vars, t) top
                               in
                            (match uu____4318 with
                             | (head_ml,head_t,args) ->
                                 (match args with
                                  | [] ->
                                      let uu____4470 =
                                        maybe_eta_data_and_project_record g
                                          qual head_t head_ml
                                         in
                                      (uu____4470,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        head_t)
                                  | uu____4471 ->
                                      extract_app_maybe_projector qual
                                        head_ml
                                        (FStar_Extraction_ML_Syntax.E_PURE,
                                          head_t) args)))
                   | uu____4477 ->
                       let uu____4478 = term_as_mlexpr g head  in
                       (match uu____4478 with
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
           let uu____4526 = check_term_as_mlexpr g e0 f t  in
           (match uu____4526 with | (e,t) -> (e, f, t))
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
                   let lb =
                     let uu___146_4567 = lb  in
                     {
                       FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                       FStar_Syntax_Syntax.lbunivs =
                         (uu___146_4567.FStar_Syntax_Syntax.lbunivs);
                       FStar_Syntax_Syntax.lbtyp =
                         (uu___146_4567.FStar_Syntax_Syntax.lbtyp);
                       FStar_Syntax_Syntax.lbeff =
                         (uu___146_4567.FStar_Syntax_Syntax.lbeff);
                       FStar_Syntax_Syntax.lbdef =
                         (uu___146_4567.FStar_Syntax_Syntax.lbdef)
                     }  in
                   let e' =
                     FStar_Syntax_Subst.subst
                       [FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x)] e'
                      in
                   ([lb], e')))
              in
           (match uu____4547 with
            | (lbs,e') ->
                let lbs =
                  if top_level
                  then
                    FStar_All.pipe_right lbs
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
                             let uu___147_4596 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___147_4596.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___147_4596.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___147_4596.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___147_4596.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef
                             })))
                  else lbs  in
                let maybe_generalize uu____4610 =
                  match uu____4610 with
                  | { FStar_Syntax_Syntax.lbname = lbname_;
                      FStar_Syntax_Syntax.lbunivs = uu____4621;
                      FStar_Syntax_Syntax.lbtyp = t;
                      FStar_Syntax_Syntax.lbeff = lbeff;
                      FStar_Syntax_Syntax.lbdef = e;_} ->
                      let f_e = effect_as_etag g lbeff  in
                      let t = FStar_Syntax_Subst.compress t  in
                      (match t.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                           let uu____4664 = FStar_List.hd bs  in
                           FStar_All.pipe_right uu____4664 (is_type_binder g)
                           ->
                           let uu____4671 = FStar_Syntax_Subst.open_comp bs c
                              in
                           (match uu____4671 with
                            | (bs,c) ->
                                let uu____4685 =
                                  let uu____4690 =
                                    FStar_Util.prefix_until
                                      (fun x  ->
                                         let uu____4708 = is_type_binder g x
                                            in
                                         Prims.op_Negation uu____4708) bs
                                     in
                                  match uu____4690 with
                                  | None  ->
                                      (bs, (FStar_Syntax_Util.comp_result c))
                                  | Some (bs,b,rest) ->
                                      let uu____4756 =
                                        FStar_Syntax_Util.arrow (b :: rest) c
                                         in
                                      (bs, uu____4756)
                                   in
                                (match uu____4685 with
                                 | (tbinders,tbody) ->
                                     let n_tbinders =
                                       FStar_List.length tbinders  in
                                     let e =
                                       let uu____4786 = normalize_abs e  in
                                       FStar_All.pipe_right uu____4786
                                         FStar_Syntax_Util.unmeta
                                        in
                                     (match e.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Tm_abs
                                          (bs,body,uu____4798) ->
                                          let uu____4821 =
                                            FStar_Syntax_Subst.open_term bs
                                              body
                                             in
                                          (match uu____4821 with
                                           | (bs,body) ->
                                               if
                                                 n_tbinders <=
                                                   (FStar_List.length bs)
                                               then
                                                 let uu____4851 =
                                                   FStar_Util.first_N
                                                     n_tbinders bs
                                                    in
                                                 (match uu____4851 with
                                                  | (targs,rest_args) ->
                                                      let expected_source_ty
                                                        =
                                                        let s =
                                                          FStar_List.map2
                                                            (fun uu____4894 
                                                               ->
                                                               fun uu____4895
                                                                  ->
                                                                 match 
                                                                   (uu____4894,
                                                                    uu____4895)
                                                                 with
                                                                 | ((x,uu____4905),
                                                                    (y,uu____4907))
                                                                    ->
                                                                    let uu____4912
                                                                    =
                                                                    let uu____4917
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    y  in
                                                                    (x,
                                                                    uu____4917)
                                                                     in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____4912)
                                                            tbinders targs
                                                           in
                                                        FStar_Syntax_Subst.subst
                                                          s tbody
                                                         in
                                                      let env =
                                                        FStar_List.fold_left
                                                          (fun env  ->
                                                             fun uu____4922 
                                                               ->
                                                               match uu____4922
                                                               with
                                                               | (a,uu____4926)
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
                                                        let uu____4934 =
                                                          FStar_All.pipe_right
                                                            targs
                                                            (FStar_List.map
                                                               (fun
                                                                  uu____4948 
                                                                  ->
                                                                  match uu____4948
                                                                  with
                                                                  | (x,uu____4954)
                                                                    ->
                                                                    FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                                    x))
                                                           in
                                                        (uu____4934,
                                                          expected_t)
                                                         in
                                                      let add_unit =
                                                        match rest_args with
                                                        | [] ->
                                                            let uu____4961 =
                                                              is_fstar_value
                                                                body
                                                               in
                                                            Prims.op_Negation
                                                              uu____4961
                                                        | uu____4962 -> false
                                                         in
                                                      let rest_args =
                                                        if add_unit
                                                        then unit_binder ::
                                                          rest_args
                                                        else rest_args  in
                                                      let body =
                                                        match rest_args with
                                                        | [] -> body
                                                        | uu____4971 ->
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
                                                 fun uu____5027  ->
                                                   match uu____5027 with
                                                   | (a,uu____5031) ->
                                                       FStar_Extraction_ML_UEnv.extend_ty
                                                         env a None) g
                                              tbinders
                                             in
                                          let expected_t =
                                            term_as_mlty env tbody  in
                                          let polytype =
                                            let uu____5039 =
                                              FStar_All.pipe_right tbinders
                                                (FStar_List.map
                                                   (fun uu____5050  ->
                                                      match uu____5050 with
                                                      | (x,uu____5056) ->
                                                          FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                            x))
                                               in
                                            (uu____5039, expected_t)  in
                                          let args =
                                            FStar_All.pipe_right tbinders
                                              (FStar_List.map
                                                 (fun uu____5065  ->
                                                    match uu____5065 with
                                                    | (bv,uu____5069) ->
                                                        let uu____5070 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            bv
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____5070
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
                                      | uu____5108 -> err_value_restriction e)))
                       | uu____5118 ->
                           let expected_t = term_as_mlty g t  in
                           (lbname_, f_e, (t, ([], ([], expected_t))), false,
                             e))
                   in
                let check_lb env uu____5175 =
                  match uu____5175 with
                  | (nm,(lbname,f,(t,(targs,polytype)),add_unit,e)) ->
                      let env =
                        FStar_List.fold_left
                          (fun env  ->
                             fun uu____5246  ->
                               match uu____5246 with
                               | (a,uu____5250) ->
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
                      let uu____5253 =
                        check_term_as_mlexpr env e f expected_t  in
                      (match uu____5253 with
                       | (e,uu____5259) ->
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
                let uu____5294 =
                  FStar_List.fold_right
                    (fun lb  ->
                       fun uu____5333  ->
                         match uu____5333 with
                         | (env,lbs) ->
                             let uu____5397 = lb  in
                             (match uu____5397 with
                              | (lbname,uu____5422,(t,(uu____5424,polytype)),add_unit,uu____5427)
                                  ->
                                  let uu____5434 =
                                    FStar_Extraction_ML_UEnv.extend_lb env
                                      lbname t polytype add_unit true
                                     in
                                  (match uu____5434 with
                                   | (env,nm) -> (env, ((nm, lb) :: lbs)))))
                    lbs (g, [])
                   in
                (match uu____5294 with
                 | (env_body,lbs) ->
                     let env_def = if is_rec then env_body else g  in
                     let lbs =
                       FStar_All.pipe_right lbs
                         (FStar_List.map (check_lb env_def))
                        in
                     let e'_rng = e'.FStar_Syntax_Syntax.pos  in
                     let uu____5577 = term_as_mlexpr env_body e'  in
                     (match uu____5577 with
                      | (e',f',t') ->
                          let f =
                            let uu____5588 =
                              let uu____5590 = FStar_List.map Prims.fst lbs
                                 in
                              f' :: uu____5590  in
                            FStar_Extraction_ML_Util.join_l e'_rng uu____5588
                             in
                          let is_rec =
                            if is_rec = true
                            then FStar_Extraction_ML_Syntax.Rec
                            else FStar_Extraction_ML_Syntax.NonRec  in
                          let uu____5596 =
                            let uu____5597 =
                              let uu____5598 =
                                let uu____5599 = FStar_List.map Prims.snd lbs
                                   in
                                (is_rec, [], uu____5599)  in
                              mk_MLE_Let top_level uu____5598 e'  in
                            let uu____5605 =
                              FStar_Extraction_ML_Util.mlloc_of_range
                                t.FStar_Syntax_Syntax.pos
                               in
                            FStar_Extraction_ML_Syntax.with_ty_loc t'
                              uu____5597 uu____5605
                             in
                          (uu____5596, f, t'))))
       | FStar_Syntax_Syntax.Tm_match (scrutinee,pats) ->
           let uu____5634 = term_as_mlexpr g scrutinee  in
           (match uu____5634 with
            | (e,f_e,t_e) ->
                let uu____5644 = check_pats_for_ite pats  in
                (match uu____5644 with
                 | (b,then_e,else_e) ->
                     let no_lift x t = x  in
                     if b
                     then
                       (match (then_e, else_e) with
                        | (Some then_e,Some else_e) ->
                            let uu____5679 = term_as_mlexpr g then_e  in
                            (match uu____5679 with
                             | (then_mle,f_then,t_then) ->
                                 let uu____5689 = term_as_mlexpr g else_e  in
                                 (match uu____5689 with
                                  | (else_mle,f_else,t_else) ->
                                      let uu____5699 =
                                        let uu____5706 =
                                          type_leq g t_then t_else  in
                                        if uu____5706
                                        then (t_else, no_lift)
                                        else
                                          (let uu____5718 =
                                             type_leq g t_else t_then  in
                                           if uu____5718
                                           then (t_then, no_lift)
                                           else
                                             (FStar_Extraction_ML_Syntax.MLTY_Top,
                                               FStar_Extraction_ML_Syntax.apply_obj_repr))
                                         in
                                      (match uu____5699 with
                                       | (t_branch,maybe_lift) ->
                                           let uu____5747 =
                                             let uu____5748 =
                                               let uu____5749 =
                                                 let uu____5754 =
                                                   maybe_lift then_mle t_then
                                                    in
                                                 let uu____5755 =
                                                   let uu____5757 =
                                                     maybe_lift else_mle
                                                       t_else
                                                      in
                                                   Some uu____5757  in
                                                 (e, uu____5754, uu____5755)
                                                  in
                                               FStar_Extraction_ML_Syntax.MLE_If
                                                 uu____5749
                                                in
                                             FStar_All.pipe_left
                                               (FStar_Extraction_ML_Syntax.with_ty
                                                  t_branch) uu____5748
                                              in
                                           let uu____5759 =
                                             FStar_Extraction_ML_Util.join
                                               then_e.FStar_Syntax_Syntax.pos
                                               f_then f_else
                                              in
                                           (uu____5747, uu____5759, t_branch))))
                        | uu____5760 ->
                            failwith
                              "ITE pats matched but then and else expressions not found?")
                     else
                       (let uu____5769 =
                          FStar_All.pipe_right pats
                            (FStar_Util.fold_map
                               (fun compat  ->
                                  fun br  ->
                                    let uu____5819 =
                                      FStar_Syntax_Subst.open_branch br  in
                                    match uu____5819 with
                                    | (pat,when_opt,branch) ->
                                        let uu____5849 =
                                          extract_pat g pat t_e  in
                                        (match uu____5849 with
                                         | (env,p,pat_t_compat) ->
                                             let uu____5880 =
                                               match when_opt with
                                               | None  ->
                                                   (None,
                                                     FStar_Extraction_ML_Syntax.E_PURE)
                                               | Some w ->
                                                   let uu____5895 =
                                                     term_as_mlexpr env w  in
                                                   (match uu____5895 with
                                                    | (w,f_w,t_w) ->
                                                        let w =
                                                          maybe_coerce env w
                                                            t_w
                                                            FStar_Extraction_ML_Syntax.ml_bool_ty
                                                           in
                                                        ((Some w), f_w))
                                                in
                                             (match uu____5880 with
                                              | (when_opt,f_when) ->
                                                  let uu____5923 =
                                                    term_as_mlexpr env branch
                                                     in
                                                  (match uu____5923 with
                                                   | (mlbranch,f_branch,t_branch)
                                                       ->
                                                       let uu____5942 =
                                                         FStar_All.pipe_right
                                                           p
                                                           (FStar_List.map
                                                              (fun uu____5979
                                                                  ->
                                                                 match uu____5979
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
                                                         uu____5942))))) true)
                           in
                        match uu____5769 with
                        | (pat_t_compat,mlbranches) ->
                            let mlbranches = FStar_List.flatten mlbranches
                               in
                            let e =
                              if pat_t_compat
                              then e
                              else
                                (FStar_Extraction_ML_UEnv.debug g
                                   (fun uu____6065  ->
                                      let uu____6066 =
                                        FStar_Extraction_ML_Code.string_of_mlexpr
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          e
                                         in
                                      let uu____6067 =
                                        FStar_Extraction_ML_Code.string_of_mlty
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          t_e
                                         in
                                      FStar_Util.print2
                                        "Coercing scrutinee %s from type %s because pattern type is incompatible\n"
                                        uu____6066 uu____6067);
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty t_e)
                                   (FStar_Extraction_ML_Syntax.MLE_Coerce
                                      (e, t_e,
                                        FStar_Extraction_ML_Syntax.MLTY_Top)))
                               in
                            (match mlbranches with
                             | [] ->
                                 let uu____6080 =
                                   let uu____6085 =
                                     let uu____6094 =
                                       FStar_Syntax_Syntax.lid_as_fv
                                         FStar_Syntax_Const.failwith_lid
                                         FStar_Syntax_Syntax.Delta_constant
                                         None
                                        in
                                     FStar_Extraction_ML_UEnv.lookup_fv g
                                       uu____6094
                                      in
                                   FStar_All.pipe_left FStar_Util.right
                                     uu____6085
                                    in
                                 (match uu____6080 with
                                  | (uu____6116,fw,uu____6118,uu____6119) ->
                                      let uu____6120 =
                                        let uu____6121 =
                                          let uu____6122 =
                                            let uu____6126 =
                                              let uu____6128 =
                                                FStar_All.pipe_left
                                                  (FStar_Extraction_ML_Syntax.with_ty
                                                     FStar_Extraction_ML_Syntax.ml_string_ty)
                                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                                     (FStar_Extraction_ML_Syntax.MLC_String
                                                        "unreachable"))
                                                 in
                                              [uu____6128]  in
                                            (fw, uu____6126)  in
                                          FStar_Extraction_ML_Syntax.MLE_App
                                            uu____6122
                                           in
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             FStar_Extraction_ML_Syntax.ml_unit_ty)
                                          uu____6121
                                         in
                                      (uu____6120,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        FStar_Extraction_ML_Syntax.ml_unit_ty))
                             | (uu____6130,uu____6131,(uu____6132,f_first,t_first))::rest
                                 ->
                                 let uu____6164 =
                                   FStar_List.fold_left
                                     (fun uu____6180  ->
                                        fun uu____6181  ->
                                          match (uu____6180, uu____6181) with
                                          | ((topt,f),(uu____6211,uu____6212,
                                                       (uu____6213,f_branch,t_branch)))
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
                                                    let uu____6244 =
                                                      type_leq g t t_branch
                                                       in
                                                    if uu____6244
                                                    then Some t_branch
                                                    else
                                                      (let uu____6247 =
                                                         type_leq g t_branch
                                                           t
                                                          in
                                                       if uu____6247
                                                       then Some t
                                                       else None)
                                                 in
                                              (topt, f))
                                     ((Some t_first), f_first) rest
                                    in
                                 (match uu____6164 with
                                  | (topt,f_match) ->
                                      let mlbranches =
                                        FStar_All.pipe_right mlbranches
                                          (FStar_List.map
                                             (fun uu____6293  ->
                                                match uu____6293 with
                                                | (p,(wopt,uu____6309),
                                                   (b,uu____6311,t)) ->
                                                    let b =
                                                      match topt with
                                                      | None  ->
                                                          FStar_Extraction_ML_Syntax.apply_obj_repr
                                                            b t
                                                      | Some uu____6322 -> b
                                                       in
                                                    (p, wopt, b)))
                                         in
                                      let t_match =
                                        match topt with
                                        | None  ->
                                            FStar_Extraction_ML_Syntax.MLTY_Top
                                        | Some t -> t  in
                                      let uu____6326 =
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             t_match)
                                          (FStar_Extraction_ML_Syntax.MLE_Match
                                             (e, mlbranches))
                                         in
                                      (uu____6326, f_match, t_match)))))))

let fresh : Prims.string -> (Prims.string * Prims.int) =
  let c = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun x  ->
    FStar_Util.incr c; (let uu____6344 = FStar_ST.read c  in (x, uu____6344))
  
let ind_discriminator_body :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlmodule1
  =
  fun env  ->
    fun discName  ->
      fun constrName  ->
        let uu____6356 =
          FStar_TypeChecker_Env.lookup_lid env.FStar_Extraction_ML_UEnv.tcenv
            discName
           in
        match uu____6356 with
        | (uu____6359,fstar_disc_type) ->
            let wildcards =
              let uu____6367 =
                let uu____6368 = FStar_Syntax_Subst.compress fstar_disc_type
                   in
                uu____6368.FStar_Syntax_Syntax.n  in
              match uu____6367 with
              | FStar_Syntax_Syntax.Tm_arrow (binders,uu____6377) ->
                  let uu____6388 =
                    FStar_All.pipe_right binders
                      (FStar_List.filter
                         (fun uu___141_6403  ->
                            match uu___141_6403 with
                            | (uu____6407,Some (FStar_Syntax_Syntax.Implicit
                               uu____6408)) -> true
                            | uu____6410 -> false))
                     in
                  FStar_All.pipe_right uu____6388
                    (FStar_List.map
                       (fun uu____6430  ->
                          let uu____6434 = fresh "_"  in
                          (uu____6434, FStar_Extraction_ML_Syntax.MLTY_Top)))
              | uu____6439 -> failwith "Discriminator must be a function"  in
            let mlid = fresh "_discr_"  in
            let targ = FStar_Extraction_ML_Syntax.MLTY_Top  in
            let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top  in
            let discrBody =
              let uu____6451 =
                let uu____6452 =
                  let uu____6458 =
                    let uu____6459 =
                      let uu____6460 =
                        let uu____6468 =
                          let uu____6469 =
                            let uu____6470 =
                              let uu____6471 =
                                FStar_Extraction_ML_Syntax.idsym mlid  in
                              ([], uu____6471)  in
                            FStar_Extraction_ML_Syntax.MLE_Name uu____6470
                             in
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty targ)
                            uu____6469
                           in
                        let uu____6473 =
                          let uu____6479 =
                            let uu____6484 =
                              let uu____6485 =
                                let uu____6489 =
                                  FStar_Extraction_ML_Syntax.mlpath_of_lident
                                    constrName
                                   in
                                (uu____6489,
                                  [FStar_Extraction_ML_Syntax.MLP_Wild])
                                 in
                              FStar_Extraction_ML_Syntax.MLP_CTor uu____6485
                               in
                            let uu____6491 =
                              FStar_All.pipe_left
                                (FStar_Extraction_ML_Syntax.with_ty
                                   FStar_Extraction_ML_Syntax.ml_bool_ty)
                                (FStar_Extraction_ML_Syntax.MLE_Const
                                   (FStar_Extraction_ML_Syntax.MLC_Bool true))
                               in
                            (uu____6484, None, uu____6491)  in
                          let uu____6493 =
                            let uu____6499 =
                              let uu____6504 =
                                FStar_All.pipe_left
                                  (FStar_Extraction_ML_Syntax.with_ty
                                     FStar_Extraction_ML_Syntax.ml_bool_ty)
                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                     (FStar_Extraction_ML_Syntax.MLC_Bool
                                        false))
                                 in
                              (FStar_Extraction_ML_Syntax.MLP_Wild, None,
                                uu____6504)
                               in
                            [uu____6499]  in
                          uu____6479 :: uu____6493  in
                        (uu____6468, uu____6473)  in
                      FStar_Extraction_ML_Syntax.MLE_Match uu____6460  in
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.ml_bool_ty) uu____6459
                     in
                  ((FStar_List.append wildcards [(mlid, targ)]), uu____6458)
                   in
                FStar_Extraction_ML_Syntax.MLE_Fun uu____6452  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty disc_ty) uu____6451
               in
            let uu____6542 =
              let uu____6543 =
                let uu____6545 =
                  let uu____6546 =
                    FStar_Extraction_ML_UEnv.convIdent
                      discName.FStar_Ident.ident
                     in
                  {
                    FStar_Extraction_ML_Syntax.mllb_name = uu____6546;
                    FStar_Extraction_ML_Syntax.mllb_tysc = None;
                    FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                    FStar_Extraction_ML_Syntax.mllb_def = discrBody;
                    FStar_Extraction_ML_Syntax.print_typ = false
                  }  in
                [uu____6545]  in
              (FStar_Extraction_ML_Syntax.NonRec, [], uu____6543)  in
            FStar_Extraction_ML_Syntax.MLM_Let uu____6542
  