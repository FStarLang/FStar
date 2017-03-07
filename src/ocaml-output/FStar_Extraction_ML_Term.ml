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
  (let uu____78 =
     let uu____79 = FStar_Range.string_of_range r in
     FStar_Util.format2 "%s: %s\n" uu____79 msg in
   FStar_All.pipe_left FStar_Util.print_string uu____78);
  failwith msg
let err_uninst env t uu____107 app =
  match uu____107 with
  | (vars,ty) ->
      let uu____122 =
        let uu____123 = FStar_Syntax_Print.term_to_string t in
        let uu____124 =
          let uu____125 =
            FStar_All.pipe_right vars (FStar_List.map Prims.fst) in
          FStar_All.pipe_right uu____125 (FStar_String.concat ", ") in
        let uu____134 =
          FStar_Extraction_ML_Code.string_of_mlty
            env.FStar_Extraction_ML_UEnv.currentModule ty in
        let uu____135 = FStar_Syntax_Print.term_to_string app in
        FStar_Util.format4
          "Variable %s has a polymorphic type (forall %s. %s); expected it to be fully instantiated, but got %s"
          uu____123 uu____124 uu____134 uu____135 in
      fail t.FStar_Syntax_Syntax.pos uu____122
let err_ill_typed_application env t args ty =
  let uu____166 =
    let uu____167 = FStar_Syntax_Print.term_to_string t in
    let uu____168 =
      let uu____169 =
        FStar_All.pipe_right args
          (FStar_List.map
             (fun uu____177  ->
                match uu____177 with
                | (x,uu____181) -> FStar_Syntax_Print.term_to_string x)) in
      FStar_All.pipe_right uu____169 (FStar_String.concat " ") in
    let uu____183 =
      FStar_Extraction_ML_Code.string_of_mlty
        env.FStar_Extraction_ML_UEnv.currentModule ty in
    FStar_Util.format3
      "Ill-typed application: application is %s \n remaining args are %s\nml type of head is %s\n"
      uu____167 uu____168 uu____183 in
  fail t.FStar_Syntax_Syntax.pos uu____166
let err_value_restriction t =
  let uu____195 =
    let uu____196 = FStar_Syntax_Print.tag_of_term t in
    let uu____197 = FStar_Syntax_Print.term_to_string t in
    FStar_Util.format2
      "Refusing to generalize because of the value restriction: (%s) %s"
      uu____196 uu____197 in
  fail t.FStar_Syntax_Syntax.pos uu____195
let err_unexpected_eff t f0 f1 =
  let uu____219 =
    let uu____220 = FStar_Syntax_Print.term_to_string t in
    FStar_Util.format3 "for expression %s, Expected effect %s; got effect %s"
      uu____220 (FStar_Extraction_ML_Util.eff_to_string f0)
      (FStar_Extraction_ML_Util.eff_to_string f1) in
  fail t.FStar_Syntax_Syntax.pos uu____219
let effect_as_etag:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Ident.lident -> FStar_Extraction_ML_Syntax.e_tag
  =
  let cache = FStar_Util.smap_create (Prims.parse_int "20") in
  let rec delta_norm_eff g l =
    let uu____234 = FStar_Util.smap_try_find cache l.FStar_Ident.str in
    match uu____234 with
    | Some l -> l
    | None  ->
        let res =
          let uu____238 =
            FStar_TypeChecker_Env.lookup_effect_abbrev
              g.FStar_Extraction_ML_UEnv.tcenv [FStar_Syntax_Syntax.U_zero] l in
          match uu____238 with
          | None  -> l
          | Some (uu____244,c) ->
              delta_norm_eff g (FStar_Syntax_Util.comp_effect_name c) in
        (FStar_Util.smap_add cache l.FStar_Ident.str res; res) in
  fun g  ->
    fun l  ->
      let l = delta_norm_eff g l in
      match FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid with
      | true  -> FStar_Extraction_ML_Syntax.E_PURE
      | uu____252 ->
          (match FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GHOST_lid
           with
           | true  -> FStar_Extraction_ML_Syntax.E_GHOST
           | uu____253 -> FStar_Extraction_ML_Syntax.E_IMPURE)
let rec is_arity:
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let t = FStar_Syntax_Util.unmeta t in
      let uu____261 =
        let uu____262 = FStar_Syntax_Subst.compress t in
        uu____262.FStar_Syntax_Syntax.n in
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
              env.FStar_Extraction_ML_UEnv.tcenv t in
          let uu____287 =
            let uu____288 = FStar_Syntax_Subst.compress t in
            uu____288.FStar_Syntax_Syntax.n in
          (match uu____287 with
           | FStar_Syntax_Syntax.Tm_fvar uu____291 -> false
           | uu____292 -> is_arity env t)
      | FStar_Syntax_Syntax.Tm_app uu____293 ->
          let uu____303 = FStar_Syntax_Util.head_and_args t in
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
let rec is_type_aux:
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let t = FStar_Syntax_Subst.compress t in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed _|FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____452 =
            let uu____453 = FStar_Syntax_Print.tag_of_term t in
            FStar_Util.format1 "Impossible: %s" uu____453 in
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
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____460 with
           | true  -> true
           | uu____465 ->
               let uu____466 =
                 FStar_TypeChecker_Env.lookup_lid
                   env.FStar_Extraction_ML_UEnv.tcenv
                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
               (match uu____466 with | (uu____473,t) -> is_arity env t))
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
let is_type:
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let b = is_type_aux env t in
      FStar_Extraction_ML_UEnv.debug env
        (fun uu____666  ->
           match b with
           | true  ->
               let uu____667 = FStar_Syntax_Print.term_to_string t in
               let uu____668 = FStar_Syntax_Print.tag_of_term t in
               FStar_Util.print2 "is_type %s (%s)\n" uu____667 uu____668
           | uu____669 ->
               let uu____670 = FStar_Syntax_Print.term_to_string t in
               let uu____671 = FStar_Syntax_Print.tag_of_term t in
               FStar_Util.print2 "not a type %s (%s)\n" uu____670 uu____671);
      b
let is_type_binder env x =
  is_arity env (Prims.fst x).FStar_Syntax_Syntax.sort
let is_constructor: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____691 =
      let uu____692 = FStar_Syntax_Subst.compress t in
      uu____692.FStar_Syntax_Syntax.n in
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
let rec is_fstar_value: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____704 =
      let uu____705 = FStar_Syntax_Subst.compress t in
      uu____705.FStar_Syntax_Syntax.n in
    match uu____704 with
    | FStar_Syntax_Syntax.Tm_constant _
      |FStar_Syntax_Syntax.Tm_bvar _
       |FStar_Syntax_Syntax.Tm_fvar _|FStar_Syntax_Syntax.Tm_abs _ -> true
    | FStar_Syntax_Syntax.Tm_app (head,args) ->
        let uu____728 = is_constructor head in
        (match uu____728 with
         | true  ->
             FStar_All.pipe_right args
               (FStar_List.for_all
                  (fun uu____736  ->
                     match uu____736 with
                     | (te,uu____740) -> is_fstar_value te))
         | uu____741 -> false)
    | FStar_Syntax_Syntax.Tm_meta (t,_)|FStar_Syntax_Syntax.Tm_ascribed
      (t,_,_) -> is_fstar_value t
    | uu____761 -> false
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
    | FStar_Extraction_ML_Syntax.MLE_Record (uu____774,fields) ->
        FStar_Util.for_all
          (fun uu____786  ->
             match uu____786 with | (uu____789,e) -> is_ml_value e) fields
    | uu____791 -> false
let normalize_abs: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t0  ->
    let rec aux bs t copt =
      let t = FStar_Syntax_Subst.compress t in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_abs (bs',body,copt) ->
          aux (FStar_List.append bs bs') body copt
      | uu____851 ->
          let e' = FStar_Syntax_Util.unascribe t in
          let uu____853 = FStar_Syntax_Util.is_fun e' in
          (match uu____853 with
           | true  -> aux bs e' copt
           | uu____854 -> FStar_Syntax_Util.abs bs e' copt) in
    aux [] t0 None
let unit_binder: FStar_Syntax_Syntax.binder =
  let uu____862 =
    FStar_Syntax_Syntax.new_bv None FStar_TypeChecker_Common.t_unit in
  FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____862
let check_pats_for_ite:
  (FStar_Syntax_Syntax.pat* FStar_Syntax_Syntax.term Prims.option*
    FStar_Syntax_Syntax.term) Prims.list ->
    (Prims.bool* FStar_Syntax_Syntax.term Prims.option*
      FStar_Syntax_Syntax.term Prims.option)
  =
  fun l  ->
    let def = (false, None, None) in
    match (FStar_List.length l) <> (Prims.parse_int "2") with
    | true  -> def
    | uu____905 ->
        let uu____906 = FStar_List.hd l in
        (match uu____906 with
         | (p1,w1,e1) ->
             let uu____925 =
               let uu____930 = FStar_List.tl l in FStar_List.hd uu____930 in
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
            let uu____1012 = erasable g f ty in
            match uu____1012 with
            | true  ->
                let uu____1013 =
                  type_leq g ty FStar_Extraction_ML_Syntax.ml_unit_ty in
                (match uu____1013 with
                 | true  -> FStar_Extraction_ML_Syntax.ml_unit
                 | uu____1014 ->
                     FStar_All.pipe_left
                       (FStar_Extraction_ML_Syntax.with_ty ty)
                       (FStar_Extraction_ML_Syntax.MLE_Coerce
                          (FStar_Extraction_ML_Syntax.ml_unit,
                            FStar_Extraction_ML_Syntax.ml_unit_ty, ty)))
            | uu____1015 -> e in
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
          let uu____1029 = (type_leq_c g (Some e) ty) expect in
          match uu____1029 with
          | (true ,Some e') -> e'
          | uu____1035 ->
              (FStar_Extraction_ML_UEnv.debug g
                 (fun uu____1040  ->
                    let uu____1041 =
                      FStar_Extraction_ML_Code.string_of_mlexpr
                        g.FStar_Extraction_ML_UEnv.currentModule e in
                    let uu____1042 =
                      FStar_Extraction_ML_Code.string_of_mlty
                        g.FStar_Extraction_ML_UEnv.currentModule ty in
                    let uu____1043 =
                      FStar_Extraction_ML_Code.string_of_mlty
                        g.FStar_Extraction_ML_UEnv.currentModule expect in
                    FStar_Util.print3
                      "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n"
                      uu____1041 uu____1042 uu____1043);
               FStar_All.pipe_left
                 (FStar_Extraction_ML_Syntax.with_ty expect)
                 (FStar_Extraction_ML_Syntax.MLE_Coerce (e, ty, expect)))
let bv_as_mlty:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlty
  =
  fun g  ->
    fun bv  ->
      let uu____1050 = FStar_Extraction_ML_UEnv.lookup_bv g bv in
      match uu____1050 with
      | FStar_Util.Inl (uu____1051,t) -> t
      | uu____1058 -> FStar_Extraction_ML_Syntax.MLTY_Top
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
      let uu____1092 =
        (fun t  ->
           match t with
           | FStar_Extraction_ML_Syntax.MLTY_Top  -> true
           | FStar_Extraction_ML_Syntax.MLTY_Named uu____1094 ->
               let uu____1098 = FStar_Extraction_ML_Util.udelta_unfold g t in
               (match uu____1098 with
                | None  -> false
                | Some t ->
                    (let rec is_top_ty t =
                       match t with
                       | FStar_Extraction_ML_Syntax.MLTY_Top  -> true
                       | FStar_Extraction_ML_Syntax.MLTY_Named uu____1105 ->
                           let uu____1109 =
                             FStar_Extraction_ML_Util.udelta_unfold g t in
                           (match uu____1109 with
                            | None  -> false
                            | Some t -> is_top_ty t)
                       | uu____1112 -> false in
                     is_top_ty) t)
           | uu____1113 -> false) mlt in
      match uu____1092 with
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
              g.FStar_Extraction_ML_UEnv.tcenv t0 in
          term_as_mlty' g t
      | uu____1115 -> mlt
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
          let uu____1121 =
            let uu____1122 = FStar_Syntax_Print.term_to_string t in
            FStar_Util.format1 "Impossible: Unexpected term %s" uu____1122 in
          failwith uu____1121
      | FStar_Syntax_Syntax.Tm_constant uu____1123 ->
          FStar_Extraction_ML_UEnv.unknownType
      | FStar_Syntax_Syntax.Tm_uvar uu____1124 ->
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
          let uu____1182 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____1182 with
           | (bs,c) ->
               let uu____1187 = binders_as_ml_binders env bs in
               (match uu____1187 with
                | (mlbs,env) ->
                    let t_ret =
                      let eff =
                        FStar_TypeChecker_Env.norm_eff_name
                          env.FStar_Extraction_ML_UEnv.tcenv
                          (FStar_Syntax_Util.comp_effect_name c) in
                      let ed =
                        FStar_TypeChecker_Env.get_effect_decl
                          env.FStar_Extraction_ML_UEnv.tcenv eff in
                      let uu____1204 =
                        FStar_All.pipe_right
                          ed.FStar_Syntax_Syntax.qualifiers
                          (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
                      match uu____1204 with
                      | true  ->
                          let t =
                            FStar_TypeChecker_Env.reify_comp
                              env.FStar_Extraction_ML_UEnv.tcenv c
                              FStar_Syntax_Syntax.U_unknown in
                          let res = term_as_mlty' env t in res
                      | uu____1208 ->
                          term_as_mlty' env (FStar_Syntax_Util.comp_result c) in
                    let erase =
                      effect_as_etag env
                        (FStar_Syntax_Util.comp_effect_name c) in
                    let uu____1210 =
                      FStar_List.fold_right
                        (fun uu____1217  ->
                           fun uu____1218  ->
                             match (uu____1217, uu____1218) with
                             | ((uu____1229,t),(tag,t')) ->
                                 (FStar_Extraction_ML_Syntax.E_PURE,
                                   (FStar_Extraction_ML_Syntax.MLTY_Fun
                                      (t, tag, t')))) mlbs (erase, t_ret) in
                    (match uu____1210 with | (uu____1237,t) -> t)))
      | FStar_Syntax_Syntax.Tm_app (head,args) ->
          let res =
            let uu____1256 =
              let uu____1257 = FStar_Syntax_Util.un_uinst head in
              uu____1257.FStar_Syntax_Syntax.n in
            match uu____1256 with
            | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
            | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv args
            | FStar_Syntax_Syntax.Tm_app (head,args') ->
                let uu____1278 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app
                       (head, (FStar_List.append args' args))) None
                    t.FStar_Syntax_Syntax.pos in
                term_as_mlty' env uu____1278
            | uu____1294 -> FStar_Extraction_ML_UEnv.unknownType in
          res
      | FStar_Syntax_Syntax.Tm_abs (bs,ty,uu____1297) ->
          let uu____1320 = FStar_Syntax_Subst.open_term bs ty in
          (match uu____1320 with
           | (bs,ty) ->
               let uu____1325 = binders_as_ml_binders env bs in
               (match uu____1325 with | (bts,env) -> term_as_mlty' env ty))
      | FStar_Syntax_Syntax.Tm_type _
        |FStar_Syntax_Syntax.Tm_let _|FStar_Syntax_Syntax.Tm_match _ ->
          FStar_Extraction_ML_UEnv.unknownType
and arg_as_mlty:
  FStar_Extraction_ML_UEnv.env ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.aqual) ->
      FStar_Extraction_ML_Syntax.mlty
  =
  fun g  ->
    fun uu____1343  ->
      match uu____1343 with
      | (a,uu____1347) ->
          let uu____1348 = is_type g a in
          (match uu____1348 with
           | true  -> term_as_mlty' g a
           | uu____1349 -> FStar_Extraction_ML_UEnv.erasedContent)
and fv_app_as_mlty:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.args -> FStar_Extraction_ML_Syntax.mlty
  =
  fun g  ->
    fun fv  ->
      fun args  ->
        let uu____1353 =
          FStar_Syntax_Util.arrow_formals
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.ty in
        match uu____1353 with
        | (formals,t) ->
            let mlargs = FStar_List.map (arg_as_mlty g) args in
            let mlargs =
              let n_args = FStar_List.length args in
              match (FStar_List.length formals) > n_args with
              | true  ->
                  let uu____1397 = FStar_Util.first_N n_args formals in
                  (match uu____1397 with
                   | (uu____1411,rest) ->
                       let uu____1425 =
                         FStar_List.map
                           (fun uu____1429  ->
                              FStar_Extraction_ML_UEnv.erasedContent) rest in
                       FStar_List.append mlargs uu____1425)
              | uu____1432 -> mlargs in
            let nm =
              let uu____1434 =
                FStar_Extraction_ML_UEnv.maybe_mangle_type_projector g fv in
              match uu____1434 with
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
      let uu____1449 =
        FStar_All.pipe_right bs
          (FStar_List.fold_left
             (fun uu____1473  ->
                fun b  ->
                  match uu____1473 with
                  | (ml_bs,env) ->
                      let uu____1503 = is_type_binder g b in
                      (match uu____1503 with
                       | true  ->
                           let b = Prims.fst b in
                           let env =
                             FStar_Extraction_ML_UEnv.extend_ty env b
                               (Some FStar_Extraction_ML_Syntax.MLTY_Top) in
                           let ml_b =
                             let uu____1518 =
                               FStar_Extraction_ML_UEnv.bv_as_ml_termvar b in
                             (uu____1518,
                               FStar_Extraction_ML_Syntax.ml_unit_ty) in
                           ((ml_b :: ml_bs), env)
                       | uu____1532 ->
                           let b = Prims.fst b in
                           let t =
                             term_as_mlty env b.FStar_Syntax_Syntax.sort in
                           let env =
                             FStar_Extraction_ML_UEnv.extend_bv env b 
                               ([], t) false false false in
                           let ml_b =
                             let uu____1542 =
                               FStar_Extraction_ML_UEnv.bv_as_ml_termvar b in
                             (uu____1542, t) in
                           ((ml_b :: ml_bs), env))) ([], g)) in
      match uu____1449 with | (ml_bs,env) -> ((FStar_List.rev ml_bs), env)
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
      | (FStar_Extraction_ML_Syntax.MLE_Seq es1,uu____1602) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (FStar_List.append es1 [e2])
      | (uu____1604,FStar_Extraction_ML_Syntax.MLE_Seq es2) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (e1 :: es2)
      | uu____1607 -> FStar_Extraction_ML_Syntax.MLE_Seq [e1; e2]
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
                 (match body.FStar_Extraction_ML_Syntax.expr =
                          FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr
                  with
                  | true  ->
                      (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
                  | uu____1627 ->
                      (match body.FStar_Extraction_ML_Syntax.expr with
                       | FStar_Extraction_ML_Syntax.MLE_Var x when
                           x = lb.FStar_Extraction_ML_Syntax.mllb_name ->
                           (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
                       | uu____1629 when
                           (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
                             =
                             FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr
                           -> body.FStar_Extraction_ML_Syntax.expr
                       | uu____1630 ->
                           mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def
                             body))
             | uu____1631 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body))
        | uu____1633 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body)
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
           | uu____1647 ->
               (match q with
                | Some (FStar_Syntax_Syntax.Record_ctor (ty,fns)) ->
                    let path =
                      FStar_List.map FStar_Ident.text_of_id ty.FStar_Ident.ns in
                    let fs = record_fields fns pats in
                    FStar_Extraction_ML_Syntax.MLP_Record (path, fs)
                | uu____1663 -> p))
      | uu____1665 -> p
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
                  ((match Prims.op_Negation ok with
                    | true  ->
                        FStar_Extraction_ML_UEnv.debug g
                          (fun uu____1704  ->
                             let uu____1705 =
                               FStar_Extraction_ML_Code.string_of_mlty
                                 g.FStar_Extraction_ML_UEnv.currentModule t' in
                             let uu____1706 =
                               FStar_Extraction_ML_Code.string_of_mlty
                                 g.FStar_Extraction_ML_UEnv.currentModule t in
                             FStar_Util.print2
                               "Expected pattern type %s; got pattern type %s\n"
                               uu____1705 uu____1706)
                    | uu____1707 -> ());
                   ok) in
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_disj uu____1715 ->
                failwith "Impossible: Nested disjunctive pattern"
            | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int
                (c,None )) ->
                let i = FStar_Const.Const_int (c, None) in
                let x = FStar_Extraction_ML_Syntax.gensym () in
                let when_clause =
                  let uu____1740 =
                    let uu____1741 =
                      let uu____1745 =
                        let uu____1747 =
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty
                               FStar_Extraction_ML_Syntax.ml_int_ty)
                            (FStar_Extraction_ML_Syntax.MLE_Var x) in
                        let uu____1748 =
                          let uu____1750 =
                            let uu____1751 =
                              let uu____1752 =
                                FStar_Extraction_ML_Util.mlconst_of_const'
                                  p.FStar_Syntax_Syntax.p i in
                              FStar_All.pipe_left
                                (fun _0_30  ->
                                   FStar_Extraction_ML_Syntax.MLE_Const _0_30)
                                uu____1752 in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.ml_int_ty)
                              uu____1751 in
                          [uu____1750] in
                        uu____1747 :: uu____1748 in
                      (FStar_Extraction_ML_Util.prims_op_equality,
                        uu____1745) in
                    FStar_Extraction_ML_Syntax.MLE_App uu____1741 in
                  FStar_All.pipe_left
                    (FStar_Extraction_ML_Syntax.with_ty
                       FStar_Extraction_ML_Syntax.ml_bool_ty) uu____1740 in
                let uu____1754 = ok FStar_Extraction_ML_Syntax.ml_int_ty in
                (g,
                  (Some
                     ((FStar_Extraction_ML_Syntax.MLP_Var x), [when_clause])),
                  uu____1754)
            | FStar_Syntax_Syntax.Pat_constant s ->
                let t =
                  FStar_TypeChecker_TcTerm.tc_constant FStar_Range.dummyRange
                    s in
                let mlty = term_as_mlty g t in
                let uu____1766 =
                  let uu____1771 =
                    let uu____1775 =
                      let uu____1776 =
                        FStar_Extraction_ML_Util.mlconst_of_const'
                          p.FStar_Syntax_Syntax.p s in
                      FStar_Extraction_ML_Syntax.MLP_Const uu____1776 in
                    (uu____1775, []) in
                  Some uu____1771 in
                let uu____1781 = ok mlty in (g, uu____1766, uu____1781)
            | FStar_Syntax_Syntax.Pat_var x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort in
                let g =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp in
                let uu____1790 =
                  match imp with
                  | true  -> None
                  | uu____1802 ->
                      let uu____1803 =
                        let uu____1807 =
                          let uu____1808 =
                            FStar_Extraction_ML_Syntax.bv_as_mlident x in
                          FStar_Extraction_ML_Syntax.MLP_Var uu____1808 in
                        (uu____1807, []) in
                      Some uu____1803 in
                let uu____1813 = ok mlty in (g, uu____1790, uu____1813)
            | FStar_Syntax_Syntax.Pat_wild x when disjunctive_pat ->
                (g, (Some (FStar_Extraction_ML_Syntax.MLP_Wild, [])), true)
            | FStar_Syntax_Syntax.Pat_wild x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort in
                let g =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp in
                let uu____1831 =
                  match imp with
                  | true  -> None
                  | uu____1843 ->
                      let uu____1844 =
                        let uu____1848 =
                          let uu____1849 =
                            FStar_Extraction_ML_Syntax.bv_as_mlident x in
                          FStar_Extraction_ML_Syntax.MLP_Var uu____1849 in
                        (uu____1848, []) in
                      Some uu____1844 in
                let uu____1854 = ok mlty in (g, uu____1831, uu____1854)
            | FStar_Syntax_Syntax.Pat_dot_term uu____1859 -> (g, None, true)
            | FStar_Syntax_Syntax.Pat_cons (f,pats) ->
                let uu____1883 =
                  let uu____1886 = FStar_Extraction_ML_UEnv.lookup_fv g f in
                  match uu____1886 with
                  | FStar_Util.Inr
                      ({
                         FStar_Extraction_ML_Syntax.expr =
                           FStar_Extraction_ML_Syntax.MLE_Name n;
                         FStar_Extraction_ML_Syntax.mlty = uu____1890;
                         FStar_Extraction_ML_Syntax.loc = uu____1891;_},ttys,uu____1893)
                      -> (n, ttys)
                  | uu____1899 -> failwith "Expected a constructor" in
                (match uu____1883 with
                 | (d,tys) ->
                     let nTyVars = FStar_List.length (Prims.fst tys) in
                     let uu____1913 = FStar_Util.first_N nTyVars pats in
                     (match uu____1913 with
                      | (tysVarPats,restPats) ->
                          let f_ty_opt =
                            try
                              let mlty_args =
                                FStar_All.pipe_right tysVarPats
                                  (FStar_List.map
                                     (fun uu____1987  ->
                                        match uu____1987 with
                                        | (p,uu____1993) ->
                                            (match p.FStar_Syntax_Syntax.v
                                             with
                                             | FStar_Syntax_Syntax.Pat_dot_term
                                                 (uu____1998,t) ->
                                                 term_as_mlty g t
                                             | uu____2004 ->
                                                 (FStar_Extraction_ML_UEnv.debug
                                                    g
                                                    (fun uu____2006  ->
                                                       let uu____2007 =
                                                         FStar_Syntax_Print.pat_to_string
                                                           p in
                                                       FStar_Util.print1
                                                         "Pattern %s is not extractable"
                                                         uu____2007);
                                                  Prims.raise Un_extractable)))) in
                              let f_ty =
                                FStar_Extraction_ML_Util.subst tys mlty_args in
                              let uu____2009 =
                                FStar_Extraction_ML_Util.uncurry_mlty_fun
                                  f_ty in
                              Some uu____2009
                            with | Un_extractable  -> None in
                          let uu____2024 =
                            FStar_Util.fold_map
                              (fun g  ->
                                 fun uu____2039  ->
                                   match uu____2039 with
                                   | (p,imp) ->
                                       let uu____2050 =
                                         extract_one_pat disjunctive_pat true
                                           g p None in
                                       (match uu____2050 with
                                        | (g,p,uu____2066) -> (g, p))) g
                              tysVarPats in
                          (match uu____2024 with
                           | (g,tyMLPats) ->
                               let uu____2098 =
                                 FStar_Util.fold_map
                                   (fun uu____2124  ->
                                      fun uu____2125  ->
                                        match (uu____2124, uu____2125) with
                                        | ((g,f_ty_opt),(p,imp)) ->
                                            let uu____2174 =
                                              match f_ty_opt with
                                              | Some (hd::rest,res) ->
                                                  ((Some (rest, res)),
                                                    (Some hd))
                                              | uu____2206 -> (None, None) in
                                            (match uu____2174 with
                                             | (f_ty_opt,expected_ty) ->
                                                 let uu____2243 =
                                                   extract_one_pat
                                                     disjunctive_pat false g
                                                     p expected_ty in
                                                 (match uu____2243 with
                                                  | (g,p,uu____2265) ->
                                                      ((g, f_ty_opt), p))))
                                   (g, f_ty_opt) restPats in
                               (match uu____2098 with
                                | ((g,f_ty_opt),restMLPats) ->
                                    let uu____2326 =
                                      let uu____2332 =
                                        FStar_All.pipe_right
                                          (FStar_List.append tyMLPats
                                             restMLPats)
                                          (FStar_List.collect
                                             (fun uu___114_2357  ->
                                                match uu___114_2357 with
                                                | Some x -> [x]
                                                | uu____2379 -> [])) in
                                      FStar_All.pipe_right uu____2332
                                        FStar_List.split in
                                    (match uu____2326 with
                                     | (mlPats,when_clauses) ->
                                         let pat_ty_compat =
                                           match f_ty_opt with
                                           | Some ([],t) -> ok t
                                           | uu____2418 -> false in
                                         let uu____2423 =
                                           let uu____2428 =
                                             let uu____2432 =
                                               resugar_pat
                                                 f.FStar_Syntax_Syntax.fv_qual
                                                 (FStar_Extraction_ML_Syntax.MLP_CTor
                                                    (d, mlPats)) in
                                             let uu____2434 =
                                               FStar_All.pipe_right
                                                 when_clauses
                                                 FStar_List.flatten in
                                             (uu____2432, uu____2434) in
                                           Some uu____2428 in
                                         (g, uu____2423, pat_ty_compat))))))
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
          let uu____2495 = extract_one_pat disj false g p expected_t in
          match uu____2495 with
          | (g,Some (x,v),b) -> (g, (x, v), b)
          | uu____2526 -> failwith "Impossible: Unable to translate pattern" in
        let mk_when_clause whens =
          match whens with
          | [] -> None
          | hd::tl ->
              let uu____2551 =
                FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd tl in
              Some uu____2551 in
        match p.FStar_Syntax_Syntax.v with
        | FStar_Syntax_Syntax.Pat_disj [] ->
            failwith "Impossible: Empty disjunctive pattern"
        | FStar_Syntax_Syntax.Pat_disj (p::pats) ->
            let uu____2577 = extract_one_pat true g p (Some expected_t) in
            (match uu____2577 with
             | (g,p,b) ->
                 let uu____2600 =
                   FStar_Util.fold_map
                     (fun b  ->
                        fun p  ->
                          let uu____2612 =
                            extract_one_pat true g p (Some expected_t) in
                          match uu____2612 with
                          | (uu____2624,p,b') -> ((b && b'), p)) b pats in
                 (match uu____2600 with
                  | (b,ps) ->
                      let ps = p :: ps in
                      let uu____2661 =
                        FStar_All.pipe_right ps
                          (FStar_List.partition
                             (fun uu___115_2689  ->
                                match uu___115_2689 with
                                | (uu____2693,uu____2694::uu____2695) -> true
                                | uu____2698 -> false)) in
                      (match uu____2661 with
                       | (ps_when,rest) ->
                           let ps =
                             FStar_All.pipe_right ps_when
                               (FStar_List.map
                                  (fun uu____2746  ->
                                     match uu____2746 with
                                     | (x,whens) ->
                                         let uu____2757 =
                                           mk_when_clause whens in
                                         (x, uu____2757))) in
                           let res =
                             match rest with
                             | [] -> (g, ps, b)
                             | rest ->
                                 let uu____2787 =
                                   let uu____2792 =
                                     let uu____2796 =
                                       let uu____2797 =
                                         FStar_List.map Prims.fst rest in
                                       FStar_Extraction_ML_Syntax.MLP_Branch
                                         uu____2797 in
                                     (uu____2796, None) in
                                   uu____2792 :: ps in
                                 (g, uu____2787, b) in
                           res)))
        | uu____2811 ->
            let uu____2812 = extract_one_pat false g p (Some expected_t) in
            (match uu____2812 with
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
            | FStar_Extraction_ML_Syntax.MLTY_Fun (t0,uu____2894,t1) ->
                let x = FStar_Extraction_ML_Syntax.gensym () in
                let uu____2897 =
                  let uu____2903 =
                    let uu____2908 =
                      FStar_All.pipe_left
                        (FStar_Extraction_ML_Syntax.with_ty t0)
                        (FStar_Extraction_ML_Syntax.MLE_Var x) in
                    ((x, t0), uu____2908) in
                  uu____2903 :: more_args in
                eta_args uu____2897 t1
            | FStar_Extraction_ML_Syntax.MLTY_Named (uu____2915,uu____2916)
                -> ((FStar_List.rev more_args), t)
            | uu____2928 -> failwith "Impossible: Head type is not an arrow" in
          let as_record qual e =
            match ((e.FStar_Extraction_ML_Syntax.expr), qual) with
            | (FStar_Extraction_ML_Syntax.MLE_CTor (uu____2946,args),Some
               (FStar_Syntax_Syntax.Record_ctor (tyname,fields))) ->
                let path =
                  FStar_List.map FStar_Ident.text_of_id tyname.FStar_Ident.ns in
                let fields = record_fields fields args in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     e.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_Record (path, fields))
            | uu____2965 -> e in
          let resugar_and_maybe_eta qual e =
            let uu____2978 = eta_args [] residualType in
            match uu____2978 with
            | (eargs,tres) ->
                (match eargs with
                 | [] ->
                     let uu____3006 = as_record qual e in
                     FStar_Extraction_ML_Util.resugar_exp uu____3006
                 | uu____3007 ->
                     let uu____3013 = FStar_List.unzip eargs in
                     (match uu____3013 with
                      | (binders,eargs) ->
                          (match e.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_CTor (head,args)
                               ->
                               let body =
                                 let uu____3037 =
                                   let uu____3038 =
                                     FStar_All.pipe_left
                                       (FStar_Extraction_ML_Syntax.with_ty
                                          tres)
                                       (FStar_Extraction_ML_Syntax.MLE_CTor
                                          (head,
                                            (FStar_List.append args eargs))) in
                                   FStar_All.pipe_left (as_record qual)
                                     uu____3038 in
                                 FStar_All.pipe_left
                                   FStar_Extraction_ML_Util.resugar_exp
                                   uu____3037 in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    e.FStar_Extraction_ML_Syntax.mlty)
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    (binders, body))
                           | uu____3043 ->
                               failwith "Impossible: Not a constructor"))) in
          match ((mlAppExpr.FStar_Extraction_ML_Syntax.expr), qual) with
          | (uu____3045,None ) -> mlAppExpr
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____3048;
                FStar_Extraction_ML_Syntax.loc = uu____3049;_},mle::args),Some
             (FStar_Syntax_Syntax.Record_projector (constrname,f))) ->
              let f =
                FStar_Ident.lid_of_ids
                  (FStar_List.append constrname.FStar_Ident.ns [f]) in
              let fn = FStar_Extraction_ML_Util.mlpath_of_lid f in
              let proj = FStar_Extraction_ML_Syntax.MLE_Proj (mle, fn) in
              let e =
                match args with
                | [] -> proj
                | uu____3067 ->
                    let uu____3069 =
                      let uu____3073 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj in
                      (uu____3073, args) in
                    FStar_Extraction_ML_Syntax.MLE_App uu____3069 in
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
              let uu____3088 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs)) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____3088
          | (FStar_Extraction_ML_Syntax.MLE_Name mlp,Some
             (FStar_Syntax_Syntax.Data_ctor ))
            |(FStar_Extraction_ML_Syntax.MLE_Name mlp,Some
              (FStar_Syntax_Syntax.Record_ctor _)) ->
              let uu____3094 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, [])) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____3094
          | uu____3096 -> mlAppExpr
let maybe_downgrade_eff:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.e_tag ->
      FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.e_tag
  =
  fun g  ->
    fun f  ->
      fun t  ->
        let uu____3109 =
          (f = FStar_Extraction_ML_Syntax.E_GHOST) &&
            (type_leq g t FStar_Extraction_ML_Syntax.ml_unit_ty) in
        match uu____3109 with
        | true  -> FStar_Extraction_ML_Syntax.E_PURE
        | uu____3110 -> f
let rec term_as_mlexpr:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Extraction_ML_Syntax.mlexpr* FStar_Extraction_ML_Syntax.e_tag*
        FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun t  ->
      let uu____3150 = term_as_mlexpr' g t in
      match uu____3150 with
      | (e,tag,ty) ->
          let tag = maybe_downgrade_eff g tag ty in
          (FStar_Extraction_ML_UEnv.debug g
             (fun u  ->
                let uu____3163 =
                  let uu____3164 = FStar_Syntax_Print.tag_of_term t in
                  let uu____3165 = FStar_Syntax_Print.term_to_string t in
                  let uu____3166 =
                    FStar_Extraction_ML_Code.string_of_mlty
                      g.FStar_Extraction_ML_UEnv.currentModule ty in
                  FStar_Util.format4
                    "term_as_mlexpr (%s) :  %s has ML type %s and effect %s\n"
                    uu____3164 uu____3165 uu____3166
                    (FStar_Extraction_ML_Util.eff_to_string tag) in
                FStar_Util.print_string uu____3163);
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
          let uu____3173 = check_term_as_mlexpr' g t f ty in
          match uu____3173 with
          | (e,t) ->
              let uu____3180 = erase g e t f in
              (match uu____3180 with | (r,uu____3187,t) -> (r, t))
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
          let uu____3195 = term_as_mlexpr g e0 in
          match uu____3195 with
          | (e,tag,t) ->
              let tag = maybe_downgrade_eff g tag t in
              (match FStar_Extraction_ML_Util.eff_leq tag f with
               | true  ->
                   let uu____3207 = maybe_coerce g e t ty in (uu____3207, ty)
               | uu____3208 -> err_unexpected_eff e0 f tag)
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
           let uu____3218 =
             let uu____3219 =
               FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos in
             let uu____3220 = FStar_Syntax_Print.tag_of_term top in
             let uu____3221 = FStar_Syntax_Print.term_to_string top in
             FStar_Util.format3 "%s: term_as_mlexpr' (%s) :  %s \n"
               uu____3219 uu____3220 uu____3221 in
           FStar_Util.print_string uu____3218);
      (let t = FStar_Syntax_Subst.compress top in
       match t.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_unknown 
         |FStar_Syntax_Syntax.Tm_delayed _
          |FStar_Syntax_Syntax.Tm_uvar _|FStar_Syntax_Syntax.Tm_bvar _ ->
           let uu____3229 =
             let uu____3230 = FStar_Syntax_Print.tag_of_term t in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____3230 in
           failwith uu____3229
       | FStar_Syntax_Syntax.Tm_type _
         |FStar_Syntax_Syntax.Tm_refine _|FStar_Syntax_Syntax.Tm_arrow _ ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Mutable_alloc ))
           ->
           let uu____3242 = term_as_mlexpr' g t in
           (match uu____3242 with
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
            | uu____3269 -> failwith "impossible")
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,uu____3278)) ->
           let t = FStar_Syntax_Subst.compress t in
           (match t.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) when
                FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname ->
                let ed =
                  FStar_TypeChecker_Env.get_effect_decl
                    g.FStar_Extraction_ML_UEnv.tcenv m in
                let uu____3302 =
                  let uu____3303 =
                    FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
                  FStar_All.pipe_right uu____3303 Prims.op_Negation in
                (match uu____3302 with
                 | true  -> term_as_mlexpr' g t
                 | uu____3308 ->
                     let ml_result_ty_1 =
                       term_as_mlty g lb.FStar_Syntax_Syntax.lbtyp in
                     let uu____3310 =
                       term_as_mlexpr g lb.FStar_Syntax_Syntax.lbdef in
                     (match uu____3310 with
                      | (comp_1,uu____3318,uu____3319) ->
                          let uu____3320 =
                            let k =
                              let uu____3324 =
                                let uu____3328 =
                                  let uu____3329 =
                                    FStar_Util.left
                                      lb.FStar_Syntax_Syntax.lbname in
                                  FStar_All.pipe_right uu____3329
                                    FStar_Syntax_Syntax.mk_binder in
                                [uu____3328] in
                              FStar_Syntax_Util.abs uu____3324 body None in
                            let uu____3335 = term_as_mlexpr g k in
                            match uu____3335 with
                            | (ml_k,uu____3342,t_k) ->
                                let m_2 =
                                  match t_k with
                                  | FStar_Extraction_ML_Syntax.MLTY_Fun
                                      (uu____3345,uu____3346,m_2) -> m_2
                                  | uu____3348 -> failwith "Impossible" in
                                (ml_k, m_2) in
                          (match uu____3320 with
                           | (ml_k,ty) ->
                               let bind =
                                 let uu____3355 =
                                   let uu____3356 =
                                     let uu____3357 =
                                       FStar_Extraction_ML_UEnv.monad_op_name
                                         ed "bind" in
                                     FStar_All.pipe_right uu____3357
                                       Prims.fst in
                                   FStar_Extraction_ML_Syntax.MLE_Name
                                     uu____3356 in
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty
                                      FStar_Extraction_ML_Syntax.MLTY_Top)
                                   uu____3355 in
                               let uu____3362 =
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty ty)
                                   (FStar_Extraction_ML_Syntax.MLE_App
                                      (bind, [comp_1; ml_k])) in
                               (uu____3362,
                                 FStar_Extraction_ML_Syntax.E_IMPURE, ty))))
            | uu____3364 -> term_as_mlexpr' g t)
       | FStar_Syntax_Syntax.Tm_meta (t,_)|FStar_Syntax_Syntax.Tm_uinst (t,_)
           -> term_as_mlexpr' g t
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____3377 =
             FStar_TypeChecker_TcTerm.type_of_tot_term
               g.FStar_Extraction_ML_UEnv.tcenv t in
           (match uu____3377 with
            | (uu____3384,ty,uu____3386) ->
                let ml_ty = term_as_mlty g ty in
                let uu____3388 =
                  let uu____3389 =
                    let uu____3390 =
                      FStar_Extraction_ML_Util.mlconst_of_const'
                        t.FStar_Syntax_Syntax.pos c in
                    FStar_All.pipe_left
                      (fun _0_31  ->
                         FStar_Extraction_ML_Syntax.MLE_Const _0_31)
                      uu____3390 in
                  FStar_Extraction_ML_Syntax.with_ty ml_ty uu____3389 in
                (uu____3388, FStar_Extraction_ML_Syntax.E_PURE, ml_ty))
       | FStar_Syntax_Syntax.Tm_name _|FStar_Syntax_Syntax.Tm_fvar _ ->
           let uu____3393 = is_type g t in
           (match uu____3393 with
            | true  ->
                (FStar_Extraction_ML_Syntax.ml_unit,
                  FStar_Extraction_ML_Syntax.E_PURE,
                  FStar_Extraction_ML_Syntax.ml_unit_ty)
            | uu____3397 ->
                let uu____3398 = FStar_Extraction_ML_UEnv.lookup_term g t in
                (match uu____3398 with
                 | (FStar_Util.Inl uu____3405,uu____3406) ->
                     (FStar_Extraction_ML_Syntax.ml_unit,
                       FStar_Extraction_ML_Syntax.E_PURE,
                       FStar_Extraction_ML_Syntax.ml_unit_ty)
                 | (FStar_Util.Inr (x,mltys,uu____3425),qual) ->
                     (match mltys with
                      | ([],t) when t = FStar_Extraction_ML_Syntax.ml_unit_ty
                          ->
                          (FStar_Extraction_ML_Syntax.ml_unit,
                            FStar_Extraction_ML_Syntax.E_PURE, t)
                      | ([],t) ->
                          let uu____3448 =
                            maybe_eta_data_and_project_record g qual t x in
                          (uu____3448, FStar_Extraction_ML_Syntax.E_PURE, t)
                      | uu____3449 -> err_uninst g t mltys t)))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,copt) ->
           let uu____3478 = FStar_Syntax_Subst.open_term bs body in
           (match uu____3478 with
            | (bs,body) ->
                let uu____3486 = binders_as_ml_binders g bs in
                (match uu____3486 with
                 | (ml_bs,env) ->
                     let uu____3503 = term_as_mlexpr env body in
                     (match uu____3503 with
                      | (ml_body,f,t) ->
                          let uu____3513 =
                            FStar_List.fold_right
                              (fun uu____3520  ->
                                 fun uu____3521  ->
                                   match (uu____3520, uu____3521) with
                                   | ((uu____3532,targ),(f,t)) ->
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         (FStar_Extraction_ML_Syntax.MLTY_Fun
                                            (targ, f, t)))) ml_bs (f, t) in
                          (match uu____3513 with
                           | (f,tfun) ->
                               let uu____3545 =
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty tfun)
                                   (FStar_Extraction_ML_Syntax.MLE_Fun
                                      (ml_bs, ml_body)) in
                               (uu____3545, f, tfun)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.tk = uu____3549;
              FStar_Syntax_Syntax.pos = uu____3550;
              FStar_Syntax_Syntax.vars = uu____3551;_},t::[])
           ->
           let uu____3574 = term_as_mlexpr' g (Prims.fst t) in
           (match uu____3574 with
            | (ml,e_tag,mlty) ->
                (ml, FStar_Extraction_ML_Syntax.E_PURE, mlty))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____3586);
              FStar_Syntax_Syntax.tk = uu____3587;
              FStar_Syntax_Syntax.pos = uu____3588;
              FStar_Syntax_Syntax.vars = uu____3589;_},t::[])
           ->
           let uu____3612 = term_as_mlexpr' g (Prims.fst t) in
           (match uu____3612 with
            | (ml,e_tag,mlty) ->
                (ml, FStar_Extraction_ML_Syntax.E_IMPURE, mlty))
       | FStar_Syntax_Syntax.Tm_app (head,args) ->
           let is_total uu___117_3648 =
             match uu___117_3648 with
             | FStar_Util.Inl l -> FStar_Syntax_Util.is_total_lcomp l
             | FStar_Util.Inr (l,flags) ->
                 (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid)
                   ||
                   (FStar_All.pipe_right flags
                      (FStar_List.existsb
                         (fun uu___116_3666  ->
                            match uu___116_3666 with
                            | FStar_Syntax_Syntax.TOTAL  -> true
                            | uu____3667 -> false))) in
           let uu____3668 =
             let uu____3671 =
               let uu____3672 = FStar_Syntax_Subst.compress head in
               uu____3672.FStar_Syntax_Syntax.n in
             ((head.FStar_Syntax_Syntax.n), uu____3671) in
           (match uu____3668 with
            | (FStar_Syntax_Syntax.Tm_uvar uu____3678,uu____3679) ->
                let t =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.Iota;
                    FStar_TypeChecker_Normalize.Zeta;
                    FStar_TypeChecker_Normalize.EraseUniverses;
                    FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                    g.FStar_Extraction_ML_UEnv.tcenv t in
                term_as_mlexpr' g t
            | (uu____3689,FStar_Syntax_Syntax.Tm_abs (bs,uu____3691,Some lc))
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
            | uu____3720 ->
                let rec extract_app is_data uu____3748 uu____3749 restArgs =
                  match (uu____3748, uu____3749) with
                  | ((mlhead,mlargs_f),(f,t)) ->
                      (match (restArgs, t) with
                       | ([],uu____3797) ->
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
                                | uu____3811 -> false) in
                           let uu____3812 =
                             match evaluation_order_guaranteed with
                             | true  ->
                                 let uu____3825 =
                                   FStar_All.pipe_right
                                     (FStar_List.rev mlargs_f)
                                     (FStar_List.map Prims.fst) in
                                 ([], uu____3825)
                             | uu____3841 ->
                                 FStar_List.fold_left
                                   (fun uu____3850  ->
                                      fun uu____3851  ->
                                        match (uu____3850, uu____3851) with
                                        | ((lbs,out_args),(arg,f)) ->
                                            (match (f =
                                                      FStar_Extraction_ML_Syntax.E_PURE)
                                                     ||
                                                     (f =
                                                        FStar_Extraction_ML_Syntax.E_GHOST)
                                             with
                                             | true  ->
                                                 (lbs, (arg :: out_args))
                                             | uu____3904 ->
                                                 let x =
                                                   FStar_Extraction_ML_Syntax.gensym
                                                     () in
                                                 let uu____3906 =
                                                   let uu____3908 =
                                                     FStar_All.pipe_left
                                                       (FStar_Extraction_ML_Syntax.with_ty
                                                          arg.FStar_Extraction_ML_Syntax.mlty)
                                                       (FStar_Extraction_ML_Syntax.MLE_Var
                                                          x) in
                                                   uu____3908 :: out_args in
                                                 (((x, arg) :: lbs),
                                                   uu____3906))) ([], [])
                                   mlargs_f in
                           (match uu____3812 with
                            | (lbs,mlargs) ->
                                let app =
                                  let uu____3935 =
                                    FStar_All.pipe_left
                                      (FStar_Extraction_ML_Syntax.with_ty t)
                                      (FStar_Extraction_ML_Syntax.MLE_App
                                         (mlhead, mlargs)) in
                                  FStar_All.pipe_left
                                    (maybe_eta_data_and_project_record g
                                       is_data t) uu____3935 in
                                let l_app =
                                  FStar_List.fold_right
                                    (fun uu____3940  ->
                                       fun out  ->
                                         match uu____3940 with
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
                       | ((arg,uu____3953)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                          (formal_t,f',t)) when is_type g arg ->
                           let uu____3971 =
                             type_leq g formal_t
                               FStar_Extraction_ML_Syntax.ml_unit_ty in
                           (match uu____3971 with
                            | true  ->
                                let uu____3975 =
                                  let uu____3978 =
                                    FStar_Extraction_ML_Util.join
                                      arg.FStar_Syntax_Syntax.pos f f' in
                                  (uu____3978, t) in
                                extract_app is_data
                                  (mlhead,
                                    ((FStar_Extraction_ML_Syntax.ml_unit,
                                       FStar_Extraction_ML_Syntax.E_PURE) ::
                                    mlargs_f)) uu____3975 rest
                            | uu____3984 ->
                                let uu____3985 =
                                  let uu____3986 =
                                    FStar_Extraction_ML_Code.string_of_mlexpr
                                      g.FStar_Extraction_ML_UEnv.currentModule
                                      mlhead in
                                  let uu____3987 =
                                    FStar_Syntax_Print.term_to_string arg in
                                  let uu____3988 =
                                    FStar_Syntax_Print.tag_of_term arg in
                                  let uu____3989 =
                                    FStar_Extraction_ML_Code.string_of_mlty
                                      g.FStar_Extraction_ML_UEnv.currentModule
                                      formal_t in
                                  FStar_Util.format4
                                    "Impossible: ill-typed application:\n\thead=%s, arg=%s, tag=%s\n\texpected type unit, got %s"
                                    uu____3986 uu____3987 uu____3988
                                    uu____3989 in
                                failwith uu____3985)
                       | ((e0,uu____3994)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                          (tExpected,f',t)) ->
                           let r = e0.FStar_Syntax_Syntax.pos in
                           let uu____4013 = term_as_mlexpr g e0 in
                           (match uu____4013 with
                            | (e0,f0,tInferred) ->
                                let e0 =
                                  maybe_coerce g e0 tInferred tExpected in
                                let uu____4024 =
                                  let uu____4027 =
                                    FStar_Extraction_ML_Util.join_l r
                                      [f; f'; f0] in
                                  (uu____4027, t) in
                                extract_app is_data
                                  (mlhead, ((e0, f0) :: mlargs_f)) uu____4024
                                  rest)
                       | uu____4033 ->
                           let uu____4040 =
                             FStar_Extraction_ML_Util.udelta_unfold g t in
                           (match uu____4040 with
                            | Some t ->
                                extract_app is_data (mlhead, mlargs_f) 
                                  (f, t) restArgs
                            | None  ->
                                err_ill_typed_application g top restArgs t)) in
                let extract_app_maybe_projector is_data mlhead uu____4076
                  args =
                  match uu____4076 with
                  | (f,t) ->
                      (match is_data with
                       | Some (FStar_Syntax_Syntax.Record_projector
                           uu____4095) ->
                           let rec remove_implicits args f t =
                             match (args, t) with
                             | ((a0,Some (FStar_Syntax_Syntax.Implicit
                                 uu____4145))::args,FStar_Extraction_ML_Syntax.MLTY_Fun
                                (uu____4147,f',t)) ->
                                 let uu____4172 =
                                   FStar_Extraction_ML_Util.join
                                     a0.FStar_Syntax_Syntax.pos f f' in
                                 remove_implicits args uu____4172 t
                             | uu____4173 -> (args, f, t) in
                           let uu____4188 = remove_implicits args f t in
                           (match uu____4188 with
                            | (args,f,t) ->
                                extract_app is_data (mlhead, []) (f, t) args)
                       | uu____4221 ->
                           extract_app is_data (mlhead, []) (f, t) args) in
                let uu____4228 = is_type g t in
                (match uu____4228 with
                 | true  ->
                     (FStar_Extraction_ML_Syntax.ml_unit,
                       FStar_Extraction_ML_Syntax.E_PURE,
                       FStar_Extraction_ML_Syntax.ml_unit_ty)
                 | uu____4232 ->
                     let head = FStar_Syntax_Util.un_uinst head in
                     (match head.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_name _
                        |FStar_Syntax_Syntax.Tm_fvar _ ->
                          let uu____4239 =
                            let uu____4246 =
                              FStar_Extraction_ML_UEnv.lookup_term g head in
                            match uu____4246 with
                            | (FStar_Util.Inr u,q) -> (u, q)
                            | uu____4279 -> failwith "FIXME Ty" in
                          (match uu____4239 with
                           | ((head_ml,(vars,t),inst_ok),qual) ->
                               let has_typ_apps =
                                 match args with
                                 | (a,uu____4308)::uu____4309 -> is_type g a
                                 | uu____4323 -> false in
                               let uu____4329 =
                                 match vars with
                                 | uu____4346::uu____4347 when
                                     (Prims.op_Negation has_typ_apps) &&
                                       inst_ok
                                     -> (head_ml, t, args)
                                 | uu____4354 ->
                                     let n = FStar_List.length vars in
                                     (match n <= (FStar_List.length args)
                                      with
                                      | true  ->
                                          let uu____4374 =
                                            FStar_Util.first_N n args in
                                          (match uu____4374 with
                                           | (prefix,rest) ->
                                               let prefixAsMLTypes =
                                                 FStar_List.map
                                                   (fun uu____4427  ->
                                                      match uu____4427 with
                                                      | (x,uu____4431) ->
                                                          term_as_mlty g x)
                                                   prefix in
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
                                                     let uu___121_4436 =
                                                       head_ml in
                                                     {
                                                       FStar_Extraction_ML_Syntax.expr
                                                         =
                                                         (uu___121_4436.FStar_Extraction_ML_Syntax.expr);
                                                       FStar_Extraction_ML_Syntax.mlty
                                                         = t;
                                                       FStar_Extraction_ML_Syntax.loc
                                                         =
                                                         (uu___121_4436.FStar_Extraction_ML_Syntax.loc)
                                                     }
                                                 | FStar_Extraction_ML_Syntax.MLE_App
                                                     (head,{
                                                             FStar_Extraction_ML_Syntax.expr
                                                               =
                                                               FStar_Extraction_ML_Syntax.MLE_Const
                                                               (FStar_Extraction_ML_Syntax.MLC_Unit
                                                               );
                                                             FStar_Extraction_ML_Syntax.mlty
                                                               = uu____4438;
                                                             FStar_Extraction_ML_Syntax.loc
                                                               = uu____4439;_}::[])
                                                     ->
                                                     FStar_All.pipe_right
                                                       (FStar_Extraction_ML_Syntax.MLE_App
                                                          ((let uu___122_4442
                                                              = head in
                                                            {
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                (uu___122_4442.FStar_Extraction_ML_Syntax.expr);
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                =
                                                                (FStar_Extraction_ML_Syntax.MLTY_Fun
                                                                   (FStar_Extraction_ML_Syntax.ml_unit_ty,
                                                                    FStar_Extraction_ML_Syntax.E_PURE,
                                                                    t));
                                                              FStar_Extraction_ML_Syntax.loc
                                                                =
                                                                (uu___122_4442.FStar_Extraction_ML_Syntax.loc)
                                                            }),
                                                            [FStar_Extraction_ML_Syntax.ml_unit]))
                                                       (FStar_Extraction_ML_Syntax.with_ty
                                                          t)
                                                 | uu____4443 ->
                                                     failwith
                                                       "Impossible: Unexpected head term" in
                                               (head, t, rest))
                                      | uu____4449 ->
                                          err_uninst g head (vars, t) top) in
                               (match uu____4329 with
                                | (head_ml,head_t,args) ->
                                    (match args with
                                     | [] ->
                                         let uu____4481 =
                                           maybe_eta_data_and_project_record
                                             g qual head_t head_ml in
                                         (uu____4481,
                                           FStar_Extraction_ML_Syntax.E_PURE,
                                           head_t)
                                     | uu____4482 ->
                                         extract_app_maybe_projector qual
                                           head_ml
                                           (FStar_Extraction_ML_Syntax.E_PURE,
                                             head_t) args)))
                      | uu____4488 ->
                          let uu____4489 = term_as_mlexpr g head in
                          (match uu____4489 with
                           | (head,f,t) ->
                               extract_app_maybe_projector None head 
                                 (f, t) args))))
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
           let uu____4537 = check_term_as_mlexpr g e0 f t in
           (match uu____4537 with | (e,t) -> (e, f, t))
       | FStar_Syntax_Syntax.Tm_let ((is_rec,lbs),e') ->
           let top_level = FStar_Syntax_Syntax.is_top_level lbs in
           let uu____4558 =
             match is_rec with
             | true  -> FStar_Syntax_Subst.open_let_rec lbs e'
             | uu____4565 ->
                 let uu____4566 = FStar_Syntax_Syntax.is_top_level lbs in
                 (match uu____4566 with
                  | true  -> (lbs, e')
                  | uu____4573 ->
                      let lb = FStar_List.hd lbs in
                      let x =
                        let uu____4576 =
                          FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                        FStar_Syntax_Syntax.freshen_bv uu____4576 in
                      let lb =
                        let uu___123_4578 = lb in
                        {
                          FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___123_4578.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp =
                            (uu___123_4578.FStar_Syntax_Syntax.lbtyp);
                          FStar_Syntax_Syntax.lbeff =
                            (uu___123_4578.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef =
                            (uu___123_4578.FStar_Syntax_Syntax.lbdef)
                        } in
                      let e' =
                        FStar_Syntax_Subst.subst
                          [FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x)]
                          e' in
                      ([lb], e')) in
           (match uu____4558 with
            | (lbs,e') ->
                let lbs =
                  match top_level with
                  | true  ->
                      FStar_All.pipe_right lbs
                        (FStar_List.map
                           (fun lb  ->
                              let tcenv =
                                let uu____4595 =
                                  FStar_Ident.lid_of_path
                                    (FStar_List.append
                                       (Prims.fst
                                          g.FStar_Extraction_ML_UEnv.currentModule)
                                       [Prims.snd
                                          g.FStar_Extraction_ML_UEnv.currentModule])
                                    FStar_Range.dummyRange in
                                FStar_TypeChecker_Env.set_current_module
                                  g.FStar_Extraction_ML_UEnv.tcenv uu____4595 in
                              FStar_Extraction_ML_UEnv.debug g
                                (fun uu____4599  ->
                                   FStar_Options.set_option "debug_level"
                                     (FStar_Options.List
                                        [FStar_Options.String "Norm";
                                        FStar_Options.String "Extraction"]));
                              (let lbdef =
                                 let uu____4603 = FStar_Options.ml_ish () in
                                 match uu____4603 with
                                 | true  -> lb.FStar_Syntax_Syntax.lbdef
                                 | uu____4606 ->
                                     FStar_TypeChecker_Normalize.normalize
                                       [FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                                       FStar_TypeChecker_Normalize.EraseUniverses;
                                       FStar_TypeChecker_Normalize.Inlining;
                                       FStar_TypeChecker_Normalize.Eager_unfolding;
                                       FStar_TypeChecker_Normalize.Exclude
                                         FStar_TypeChecker_Normalize.Zeta;
                                       FStar_TypeChecker_Normalize.PureSubtermsWithinComputations;
                                       FStar_TypeChecker_Normalize.Primops]
                                       tcenv lb.FStar_Syntax_Syntax.lbdef in
                               let uu___124_4607 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___124_4607.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___124_4607.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___124_4607.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___124_4607.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = lbdef
                               })))
                  | uu____4608 -> lbs in
                let maybe_generalize uu____4621 =
                  match uu____4621 with
                  | { FStar_Syntax_Syntax.lbname = lbname_;
                      FStar_Syntax_Syntax.lbunivs = uu____4632;
                      FStar_Syntax_Syntax.lbtyp = t;
                      FStar_Syntax_Syntax.lbeff = lbeff;
                      FStar_Syntax_Syntax.lbdef = e;_} ->
                      let f_e = effect_as_etag g lbeff in
                      let t = FStar_Syntax_Subst.compress t in
                      (match t.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                           let uu____4675 = FStar_List.hd bs in
                           FStar_All.pipe_right uu____4675 (is_type_binder g)
                           ->
                           let uu____4682 = FStar_Syntax_Subst.open_comp bs c in
                           (match uu____4682 with
                            | (bs,c) ->
                                let uu____4696 =
                                  let uu____4701 =
                                    FStar_Util.prefix_until
                                      (fun x  ->
                                         let uu____4719 = is_type_binder g x in
                                         Prims.op_Negation uu____4719) bs in
                                  match uu____4701 with
                                  | None  ->
                                      (bs, (FStar_Syntax_Util.comp_result c))
                                  | Some (bs,b,rest) ->
                                      let uu____4767 =
                                        FStar_Syntax_Util.arrow (b :: rest) c in
                                      (bs, uu____4767) in
                                (match uu____4696 with
                                 | (tbinders,tbody) ->
                                     let n_tbinders =
                                       FStar_List.length tbinders in
                                     let e =
                                       let uu____4797 = normalize_abs e in
                                       FStar_All.pipe_right uu____4797
                                         FStar_Syntax_Util.unmeta in
                                     (match e.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Tm_abs
                                          (bs,body,uu____4809) ->
                                          let uu____4832 =
                                            FStar_Syntax_Subst.open_term bs
                                              body in
                                          (match uu____4832 with
                                           | (bs,body) ->
                                               (match n_tbinders <=
                                                        (FStar_List.length bs)
                                                with
                                                | true  ->
                                                    let uu____4862 =
                                                      FStar_Util.first_N
                                                        n_tbinders bs in
                                                    (match uu____4862 with
                                                     | (targs,rest_args) ->
                                                         let expected_source_ty
                                                           =
                                                           let s =
                                                             FStar_List.map2
                                                               (fun
                                                                  uu____4905 
                                                                  ->
                                                                  fun
                                                                    uu____4906
                                                                     ->
                                                                    match 
                                                                    (uu____4905,
                                                                    uu____4906)
                                                                    with
                                                                    | 
                                                                    ((x,uu____4916),
                                                                    (y,uu____4918))
                                                                    ->
                                                                    let uu____4923
                                                                    =
                                                                    let uu____4928
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    y in
                                                                    (x,
                                                                    uu____4928) in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____4923)
                                                               tbinders targs in
                                                           FStar_Syntax_Subst.subst
                                                             s tbody in
                                                         let env =
                                                           FStar_List.fold_left
                                                             (fun env  ->
                                                                fun
                                                                  uu____4933 
                                                                  ->
                                                                  match uu____4933
                                                                  with
                                                                  | (a,uu____4937)
                                                                    ->
                                                                    FStar_Extraction_ML_UEnv.extend_ty
                                                                    env a
                                                                    None) g
                                                             targs in
                                                         let expected_t =
                                                           term_as_mlty env
                                                             expected_source_ty in
                                                         let polytype =
                                                           let uu____4945 =
                                                             FStar_All.pipe_right
                                                               targs
                                                               (FStar_List.map
                                                                  (fun
                                                                    uu____4959
                                                                     ->
                                                                    match uu____4959
                                                                    with
                                                                    | 
                                                                    (x,uu____4965)
                                                                    ->
                                                                    FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                                    x)) in
                                                           (uu____4945,
                                                             expected_t) in
                                                         let add_unit =
                                                           match rest_args
                                                           with
                                                           | [] ->
                                                               let uu____4972
                                                                 =
                                                                 is_fstar_value
                                                                   body in
                                                               Prims.op_Negation
                                                                 uu____4972
                                                           | uu____4973 ->
                                                               false in
                                                         let rest_args =
                                                           match add_unit
                                                           with
                                                           | true  ->
                                                               unit_binder ::
                                                               rest_args
                                                           | uu____4980 ->
                                                               rest_args in
                                                         let body =
                                                           match rest_args
                                                           with
                                                           | [] -> body
                                                           | uu____4982 ->
                                                               FStar_Syntax_Util.abs
                                                                 rest_args
                                                                 body None in
                                                         (lbname_, f_e,
                                                           (t,
                                                             (targs,
                                                               polytype)),
                                                           add_unit, body))
                                                | uu____5021 ->
                                                    failwith
                                                      "Not enough type binders"))
                                      | FStar_Syntax_Syntax.Tm_uinst _
                                        |FStar_Syntax_Syntax.Tm_fvar _
                                         |FStar_Syntax_Syntax.Tm_name _ ->
                                          let env =
                                            FStar_List.fold_left
                                              (fun env  ->
                                                 fun uu____5038  ->
                                                   match uu____5038 with
                                                   | (a,uu____5042) ->
                                                       FStar_Extraction_ML_UEnv.extend_ty
                                                         env a None) g
                                              tbinders in
                                          let expected_t =
                                            term_as_mlty env tbody in
                                          let polytype =
                                            let uu____5050 =
                                              FStar_All.pipe_right tbinders
                                                (FStar_List.map
                                                   (fun uu____5061  ->
                                                      match uu____5061 with
                                                      | (x,uu____5067) ->
                                                          FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                            x)) in
                                            (uu____5050, expected_t) in
                                          let args =
                                            FStar_All.pipe_right tbinders
                                              (FStar_List.map
                                                 (fun uu____5076  ->
                                                    match uu____5076 with
                                                    | (bv,uu____5080) ->
                                                        let uu____5081 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            bv in
                                                        FStar_All.pipe_right
                                                          uu____5081
                                                          FStar_Syntax_Syntax.as_arg)) in
                                          let e =
                                            (FStar_Syntax_Syntax.mk
                                               (FStar_Syntax_Syntax.Tm_app
                                                  (e, args))) None
                                              e.FStar_Syntax_Syntax.pos in
                                          (lbname_, f_e,
                                            (t, (tbinders, polytype)), false,
                                            e)
                                      | uu____5119 -> err_value_restriction e)))
                       | uu____5129 ->
                           let expected_t = term_as_mlty g t in
                           (lbname_, f_e, (t, ([], ([], expected_t))), false,
                             e)) in
                let check_lb env uu____5186 =
                  match uu____5186 with
                  | (nm,(lbname,f,(t,(targs,polytype)),add_unit,e)) ->
                      let env =
                        FStar_List.fold_left
                          (fun env  ->
                             fun uu____5257  ->
                               match uu____5257 with
                               | (a,uu____5261) ->
                                   FStar_Extraction_ML_UEnv.extend_ty env a
                                     None) env targs in
                      let expected_t =
                        match add_unit with
                        | true  ->
                            FStar_Extraction_ML_Syntax.MLTY_Fun
                              (FStar_Extraction_ML_Syntax.ml_unit_ty,
                                FStar_Extraction_ML_Syntax.E_PURE,
                                (Prims.snd polytype))
                        | uu____5263 -> Prims.snd polytype in
                      let uu____5264 =
                        check_term_as_mlexpr env e f expected_t in
                      (match uu____5264 with
                       | (e,uu____5270) ->
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
                let uu____5305 =
                  FStar_List.fold_right
                    (fun lb  ->
                       fun uu____5344  ->
                         match uu____5344 with
                         | (env,lbs) ->
                             let uu____5408 = lb in
                             (match uu____5408 with
                              | (lbname,uu____5433,(t,(uu____5435,polytype)),add_unit,uu____5438)
                                  ->
                                  let uu____5445 =
                                    FStar_Extraction_ML_UEnv.extend_lb env
                                      lbname t polytype add_unit true in
                                  (match uu____5445 with
                                   | (env,nm) -> (env, ((nm, lb) :: lbs)))))
                    lbs (g, []) in
                (match uu____5305 with
                 | (env_body,lbs) ->
                     let env_def =
                       match is_rec with
                       | true  -> env_body
                       | uu____5549 -> g in
                     let lbs =
                       FStar_All.pipe_right lbs
                         (FStar_List.map (check_lb env_def)) in
                     let e'_rng = e'.FStar_Syntax_Syntax.pos in
                     let uu____5588 = term_as_mlexpr env_body e' in
                     (match uu____5588 with
                      | (e',f',t') ->
                          let f =
                            let uu____5599 =
                              let uu____5601 = FStar_List.map Prims.fst lbs in
                              f' :: uu____5601 in
                            FStar_Extraction_ML_Util.join_l e'_rng uu____5599 in
                          let is_rec =
                            match is_rec = true with
                            | true  -> FStar_Extraction_ML_Syntax.Rec
                            | uu____5606 -> FStar_Extraction_ML_Syntax.NonRec in
                          let uu____5607 =
                            let uu____5608 =
                              let uu____5609 =
                                let uu____5610 = FStar_List.map Prims.snd lbs in
                                (is_rec, [], uu____5610) in
                              mk_MLE_Let top_level uu____5609 e' in
                            let uu____5616 =
                              FStar_Extraction_ML_Util.mlloc_of_range
                                t.FStar_Syntax_Syntax.pos in
                            FStar_Extraction_ML_Syntax.with_ty_loc t'
                              uu____5608 uu____5616 in
                          (uu____5607, f, t'))))
       | FStar_Syntax_Syntax.Tm_match (scrutinee,pats) ->
           let uu____5645 = term_as_mlexpr g scrutinee in
           (match uu____5645 with
            | (e,f_e,t_e) ->
                let uu____5655 = check_pats_for_ite pats in
                (match uu____5655 with
                 | (b,then_e,else_e) ->
                     let no_lift x t = x in
                     (match b with
                      | true  ->
                          (match (then_e, else_e) with
                           | (Some then_e,Some else_e) ->
                               let uu____5690 = term_as_mlexpr g then_e in
                               (match uu____5690 with
                                | (then_mle,f_then,t_then) ->
                                    let uu____5700 = term_as_mlexpr g else_e in
                                    (match uu____5700 with
                                     | (else_mle,f_else,t_else) ->
                                         let uu____5710 =
                                           let uu____5717 =
                                             type_leq g t_then t_else in
                                           match uu____5717 with
                                           | true  -> (t_else, no_lift)
                                           | uu____5728 ->
                                               let uu____5729 =
                                                 type_leq g t_else t_then in
                                               (match uu____5729 with
                                                | true  -> (t_then, no_lift)
                                                | uu____5740 ->
                                                    (FStar_Extraction_ML_Syntax.MLTY_Top,
                                                      FStar_Extraction_ML_Syntax.apply_obj_repr)) in
                                         (match uu____5710 with
                                          | (t_branch,maybe_lift) ->
                                              let uu____5758 =
                                                let uu____5759 =
                                                  let uu____5760 =
                                                    let uu____5765 =
                                                      maybe_lift then_mle
                                                        t_then in
                                                    let uu____5766 =
                                                      let uu____5768 =
                                                        maybe_lift else_mle
                                                          t_else in
                                                      Some uu____5768 in
                                                    (e, uu____5765,
                                                      uu____5766) in
                                                  FStar_Extraction_ML_Syntax.MLE_If
                                                    uu____5760 in
                                                FStar_All.pipe_left
                                                  (FStar_Extraction_ML_Syntax.with_ty
                                                     t_branch) uu____5759 in
                                              let uu____5770 =
                                                FStar_Extraction_ML_Util.join
                                                  then_e.FStar_Syntax_Syntax.pos
                                                  f_then f_else in
                                              (uu____5758, uu____5770,
                                                t_branch))))
                           | uu____5771 ->
                               failwith
                                 "ITE pats matched but then and else expressions not found?")
                      | uu____5779 ->
                          let uu____5780 =
                            FStar_All.pipe_right pats
                              (FStar_Util.fold_map
                                 (fun compat  ->
                                    fun br  ->
                                      let uu____5830 =
                                        FStar_Syntax_Subst.open_branch br in
                                      match uu____5830 with
                                      | (pat,when_opt,branch) ->
                                          let uu____5860 =
                                            extract_pat g pat t_e in
                                          (match uu____5860 with
                                           | (env,p,pat_t_compat) ->
                                               let uu____5891 =
                                                 match when_opt with
                                                 | None  ->
                                                     (None,
                                                       FStar_Extraction_ML_Syntax.E_PURE)
                                                 | Some w ->
                                                     let uu____5906 =
                                                       term_as_mlexpr env w in
                                                     (match uu____5906 with
                                                      | (w,f_w,t_w) ->
                                                          let w =
                                                            maybe_coerce env
                                                              w t_w
                                                              FStar_Extraction_ML_Syntax.ml_bool_ty in
                                                          ((Some w), f_w)) in
                                               (match uu____5891 with
                                                | (when_opt,f_when) ->
                                                    let uu____5934 =
                                                      term_as_mlexpr env
                                                        branch in
                                                    (match uu____5934 with
                                                     | (mlbranch,f_branch,t_branch)
                                                         ->
                                                         let uu____5953 =
                                                           FStar_All.pipe_right
                                                             p
                                                             (FStar_List.map
                                                                (fun
                                                                   uu____5990
                                                                    ->
                                                                   match uu____5990
                                                                   with
                                                                   | 
                                                                   (p,wopt)
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
                                                           uu____5953)))))
                                 true) in
                          (match uu____5780 with
                           | (pat_t_compat,mlbranches) ->
                               let mlbranches = FStar_List.flatten mlbranches in
                               let e =
                                 match pat_t_compat with
                                 | true  -> e
                                 | uu____6074 ->
                                     (FStar_Extraction_ML_UEnv.debug g
                                        (fun uu____6076  ->
                                           let uu____6077 =
                                             FStar_Extraction_ML_Code.string_of_mlexpr
                                               g.FStar_Extraction_ML_UEnv.currentModule
                                               e in
                                           let uu____6078 =
                                             FStar_Extraction_ML_Code.string_of_mlty
                                               g.FStar_Extraction_ML_UEnv.currentModule
                                               t_e in
                                           FStar_Util.print2
                                             "Coercing scrutinee %s from type %s because pattern type is incompatible\n"
                                             uu____6077 uu____6078);
                                      FStar_All.pipe_left
                                        (FStar_Extraction_ML_Syntax.with_ty
                                           t_e)
                                        (FStar_Extraction_ML_Syntax.MLE_Coerce
                                           (e, t_e,
                                             FStar_Extraction_ML_Syntax.MLTY_Top))) in
                               (match mlbranches with
                                | [] ->
                                    let uu____6091 =
                                      let uu____6095 =
                                        let uu____6103 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            FStar_Syntax_Const.failwith_lid
                                            FStar_Syntax_Syntax.Delta_constant
                                            None in
                                        FStar_Extraction_ML_UEnv.lookup_fv g
                                          uu____6103 in
                                      FStar_All.pipe_left FStar_Util.right
                                        uu____6095 in
                                    (match uu____6091 with
                                     | (fw,uu____6123,uu____6124) ->
                                         let uu____6125 =
                                           let uu____6126 =
                                             let uu____6127 =
                                               let uu____6131 =
                                                 let uu____6133 =
                                                   FStar_All.pipe_left
                                                     (FStar_Extraction_ML_Syntax.with_ty
                                                        FStar_Extraction_ML_Syntax.ml_string_ty)
                                                     (FStar_Extraction_ML_Syntax.MLE_Const
                                                        (FStar_Extraction_ML_Syntax.MLC_String
                                                           "unreachable")) in
                                                 [uu____6133] in
                                               (fw, uu____6131) in
                                             FStar_Extraction_ML_Syntax.MLE_App
                                               uu____6127 in
                                           FStar_All.pipe_left
                                             (FStar_Extraction_ML_Syntax.with_ty
                                                FStar_Extraction_ML_Syntax.ml_unit_ty)
                                             uu____6126 in
                                         (uu____6125,
                                           FStar_Extraction_ML_Syntax.E_PURE,
                                           FStar_Extraction_ML_Syntax.ml_unit_ty))
                                | (uu____6135,uu____6136,(uu____6137,f_first,t_first))::rest
                                    ->
                                    let uu____6169 =
                                      FStar_List.fold_left
                                        (fun uu____6185  ->
                                           fun uu____6186  ->
                                             match (uu____6185, uu____6186)
                                             with
                                             | ((topt,f),(uu____6216,uu____6217,
                                                          (uu____6218,f_branch,t_branch)))
                                                 ->
                                                 let f =
                                                   FStar_Extraction_ML_Util.join
                                                     top.FStar_Syntax_Syntax.pos
                                                     f f_branch in
                                                 let topt =
                                                   match topt with
                                                   | None  -> None
                                                   | Some t ->
                                                       let uu____6249 =
                                                         type_leq g t
                                                           t_branch in
                                                       (match uu____6249 with
                                                        | true  ->
                                                            Some t_branch
                                                        | uu____6251 ->
                                                            let uu____6252 =
                                                              type_leq g
                                                                t_branch t in
                                                            (match uu____6252
                                                             with
                                                             | true  ->
                                                                 Some t
                                                             | uu____6254 ->
                                                                 None)) in
                                                 (topt, f))
                                        ((Some t_first), f_first) rest in
                                    (match uu____6169 with
                                     | (topt,f_match) ->
                                         let mlbranches =
                                           FStar_All.pipe_right mlbranches
                                             (FStar_List.map
                                                (fun uu____6298  ->
                                                   match uu____6298 with
                                                   | (p,(wopt,uu____6314),
                                                      (b,uu____6316,t)) ->
                                                       let b =
                                                         match topt with
                                                         | None  ->
                                                             FStar_Extraction_ML_Syntax.apply_obj_repr
                                                               b t
                                                         | Some uu____6327 ->
                                                             b in
                                                       (p, wopt, b))) in
                                         let t_match =
                                           match topt with
                                           | None  ->
                                               FStar_Extraction_ML_Syntax.MLTY_Top
                                           | Some t -> t in
                                         let uu____6331 =
                                           FStar_All.pipe_left
                                             (FStar_Extraction_ML_Syntax.with_ty
                                                t_match)
                                             (FStar_Extraction_ML_Syntax.MLE_Match
                                                (e, mlbranches)) in
                                         (uu____6331, f_match, t_match))))))))
let fresh: Prims.string -> (Prims.string* Prims.int) =
  let c = FStar_Util.mk_ref (Prims.parse_int "0") in
  fun x  ->
    FStar_Util.incr c; (let uu____6349 = FStar_ST.read c in (x, uu____6349))
let ind_discriminator_body:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlmodule1
  =
  fun env  ->
    fun discName  ->
      fun constrName  ->
        let uu____6361 =
          FStar_TypeChecker_Env.lookup_lid env.FStar_Extraction_ML_UEnv.tcenv
            discName in
        match uu____6361 with
        | (uu____6364,fstar_disc_type) ->
            let wildcards =
              let uu____6372 =
                let uu____6373 = FStar_Syntax_Subst.compress fstar_disc_type in
                uu____6373.FStar_Syntax_Syntax.n in
              match uu____6372 with
              | FStar_Syntax_Syntax.Tm_arrow (binders,uu____6382) ->
                  let uu____6393 =
                    FStar_All.pipe_right binders
                      (FStar_List.filter
                         (fun uu___118_6408  ->
                            match uu___118_6408 with
                            | (uu____6412,Some (FStar_Syntax_Syntax.Implicit
                               uu____6413)) -> true
                            | uu____6415 -> false)) in
                  FStar_All.pipe_right uu____6393
                    (FStar_List.map
                       (fun uu____6435  ->
                          let uu____6439 = fresh "_" in
                          (uu____6439, FStar_Extraction_ML_Syntax.MLTY_Top)))
              | uu____6444 -> failwith "Discriminator must be a function" in
            let mlid = fresh "_discr_" in
            let targ = FStar_Extraction_ML_Syntax.MLTY_Top in
            let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top in
            let discrBody =
              let uu____6456 =
                let uu____6457 =
                  let uu____6463 =
                    let uu____6464 =
                      let uu____6465 =
                        let uu____6473 =
                          let uu____6474 =
                            let uu____6475 =
                              let uu____6476 =
                                FStar_Extraction_ML_Syntax.idsym mlid in
                              ([], uu____6476) in
                            FStar_Extraction_ML_Syntax.MLE_Name uu____6475 in
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty targ)
                            uu____6474 in
                        let uu____6478 =
                          let uu____6484 =
                            let uu____6489 =
                              let uu____6490 =
                                let uu____6494 =
                                  FStar_Extraction_ML_Syntax.mlpath_of_lident
                                    constrName in
                                (uu____6494,
                                  [FStar_Extraction_ML_Syntax.MLP_Wild]) in
                              FStar_Extraction_ML_Syntax.MLP_CTor uu____6490 in
                            let uu____6496 =
                              FStar_All.pipe_left
                                (FStar_Extraction_ML_Syntax.with_ty
                                   FStar_Extraction_ML_Syntax.ml_bool_ty)
                                (FStar_Extraction_ML_Syntax.MLE_Const
                                   (FStar_Extraction_ML_Syntax.MLC_Bool true)) in
                            (uu____6489, None, uu____6496) in
                          let uu____6498 =
                            let uu____6504 =
                              let uu____6509 =
                                FStar_All.pipe_left
                                  (FStar_Extraction_ML_Syntax.with_ty
                                     FStar_Extraction_ML_Syntax.ml_bool_ty)
                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                     (FStar_Extraction_ML_Syntax.MLC_Bool
                                        false)) in
                              (FStar_Extraction_ML_Syntax.MLP_Wild, None,
                                uu____6509) in
                            [uu____6504] in
                          uu____6484 :: uu____6498 in
                        (uu____6473, uu____6478) in
                      FStar_Extraction_ML_Syntax.MLE_Match uu____6465 in
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.ml_bool_ty) uu____6464 in
                  ((FStar_List.append wildcards [(mlid, targ)]), uu____6463) in
                FStar_Extraction_ML_Syntax.MLE_Fun uu____6457 in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty disc_ty) uu____6456 in
            let uu____6547 =
              let uu____6548 =
                let uu____6550 =
                  let uu____6551 =
                    FStar_Extraction_ML_UEnv.convIdent
                      discName.FStar_Ident.ident in
                  {
                    FStar_Extraction_ML_Syntax.mllb_name = uu____6551;
                    FStar_Extraction_ML_Syntax.mllb_tysc = None;
                    FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                    FStar_Extraction_ML_Syntax.mllb_def = discrBody;
                    FStar_Extraction_ML_Syntax.print_typ = false
                  } in
                [uu____6550] in
              (FStar_Extraction_ML_Syntax.NonRec, [], uu____6548) in
            FStar_Extraction_ML_Syntax.MLM_Let uu____6547