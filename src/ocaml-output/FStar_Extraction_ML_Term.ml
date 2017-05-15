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
    | Some l1 -> l1
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
      let l1 = delta_norm_eff g l in
      if FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_PURE_lid
      then FStar_Extraction_ML_Syntax.E_PURE
      else
        if FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_GHOST_lid
        then FStar_Extraction_ML_Syntax.E_GHOST
        else
          (let ed_opt =
             FStar_TypeChecker_Env.effect_decl_opt
               g.FStar_Extraction_ML_UEnv.tcenv l1 in
           match ed_opt with
           | Some (ed,qualifiers) ->
               let uu____266 =
                 FStar_All.pipe_right qualifiers
                   (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
               if uu____266
               then FStar_Extraction_ML_Syntax.E_PURE
               else FStar_Extraction_ML_Syntax.E_IMPURE
           | None  -> FStar_Extraction_ML_Syntax.E_IMPURE)
let rec is_arity:
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t in
      let uu____279 =
        let uu____280 = FStar_Syntax_Subst.compress t1 in
        uu____280.FStar_Syntax_Syntax.n in
      match uu____279 with
      | FStar_Syntax_Syntax.Tm_unknown 
        |FStar_Syntax_Syntax.Tm_delayed _
         |FStar_Syntax_Syntax.Tm_ascribed _|FStar_Syntax_Syntax.Tm_meta _ ->
          failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_uvar _
        |FStar_Syntax_Syntax.Tm_constant _
         |FStar_Syntax_Syntax.Tm_name _|FStar_Syntax_Syntax.Tm_bvar _ ->
          false
      | FStar_Syntax_Syntax.Tm_type uu____290 -> true
      | FStar_Syntax_Syntax.Tm_arrow (uu____291,c) ->
          is_arity env (FStar_Syntax_Util.comp_result c)
      | FStar_Syntax_Syntax.Tm_fvar uu____303 ->
          let t2 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Normalize.AllowUnboundUniverses;
              FStar_TypeChecker_Normalize.EraseUniverses;
              FStar_TypeChecker_Normalize.UnfoldUntil
                FStar_Syntax_Syntax.Delta_constant]
              env.FStar_Extraction_ML_UEnv.tcenv t1 in
          let uu____305 =
            let uu____306 = FStar_Syntax_Subst.compress t2 in
            uu____306.FStar_Syntax_Syntax.n in
          (match uu____305 with
           | FStar_Syntax_Syntax.Tm_fvar uu____309 -> false
           | uu____310 -> is_arity env t2)
      | FStar_Syntax_Syntax.Tm_app uu____311 ->
          let uu____321 = FStar_Syntax_Util.head_and_args t1 in
          (match uu____321 with | (head1,uu____332) -> is_arity env head1)
      | FStar_Syntax_Syntax.Tm_uinst (head1,uu____348) -> is_arity env head1
      | FStar_Syntax_Syntax.Tm_refine (x,uu____354) ->
          is_arity env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_abs (_,body,_)|FStar_Syntax_Syntax.Tm_let
        (_,body) -> is_arity env body
      | FStar_Syntax_Syntax.Tm_match (uu____383,branches) ->
          (match branches with
           | (uu____411,uu____412,e)::uu____414 -> is_arity env e
           | uu____450 -> false)
let rec is_type_aux:
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Subst.compress t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed _|FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____470 =
            let uu____471 = FStar_Syntax_Print.tag_of_term t1 in
            FStar_Util.format1 "Impossible: %s" uu____471 in
          failwith uu____470
      | FStar_Syntax_Syntax.Tm_constant uu____472 -> false
      | FStar_Syntax_Syntax.Tm_type _
        |FStar_Syntax_Syntax.Tm_refine _|FStar_Syntax_Syntax.Tm_arrow _ ->
          true
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.failwith_lid ->
          false
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____478 =
            FStar_TypeChecker_Env.is_type_constructor
              env.FStar_Extraction_ML_UEnv.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          if uu____478
          then true
          else
            (let uu____484 =
               FStar_TypeChecker_Env.lookup_lid
                 env.FStar_Extraction_ML_UEnv.tcenv
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
             match uu____484 with
             | ((uu____493,t2),uu____495) -> is_arity env t2)
      | FStar_Syntax_Syntax.Tm_uvar (_,t2)
        |FStar_Syntax_Syntax.Tm_bvar
         { FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _;
           FStar_Syntax_Syntax.sort = t2;_}|FStar_Syntax_Syntax.Tm_name
         { FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _;
           FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____517,uu____518) ->
          is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____548) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_abs (uu____553,body,uu____555) ->
          is_type_aux env body
      | FStar_Syntax_Syntax.Tm_let (uu____578,body) -> is_type_aux env body
      | FStar_Syntax_Syntax.Tm_match (uu____590,branches) ->
          (match branches with
           | (uu____618,uu____619,e)::uu____621 -> is_type_aux env e
           | uu____657 -> false)
      | FStar_Syntax_Syntax.Tm_meta (t2,uu____670) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_app (head1,uu____676) -> is_type_aux env head1
let is_type:
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let b = is_type_aux env t in
      FStar_Extraction_ML_UEnv.debug env
        (fun uu____699  ->
           if b
           then
             let uu____700 = FStar_Syntax_Print.term_to_string t in
             let uu____701 = FStar_Syntax_Print.tag_of_term t in
             FStar_Util.print2 "is_type %s (%s)\n" uu____700 uu____701
           else
             (let uu____703 = FStar_Syntax_Print.term_to_string t in
              let uu____704 = FStar_Syntax_Print.tag_of_term t in
              FStar_Util.print2 "not a type %s (%s)\n" uu____703 uu____704));
      b
let is_type_binder env x =
  is_arity env (Prims.fst x).FStar_Syntax_Syntax.sort
let is_constructor: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____724 =
      let uu____725 = FStar_Syntax_Subst.compress t in
      uu____725.FStar_Syntax_Syntax.n in
    match uu____724 with
    | FStar_Syntax_Syntax.Tm_fvar
      { FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _;
        FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor );_}
      |FStar_Syntax_Syntax.Tm_fvar
      { FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _;
        FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor
          _);_}
        -> true
    | uu____733 -> false
let rec is_fstar_value: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____737 =
      let uu____738 = FStar_Syntax_Subst.compress t in
      uu____738.FStar_Syntax_Syntax.n in
    match uu____737 with
    | FStar_Syntax_Syntax.Tm_constant _
      |FStar_Syntax_Syntax.Tm_bvar _
       |FStar_Syntax_Syntax.Tm_fvar _|FStar_Syntax_Syntax.Tm_abs _ -> true
    | FStar_Syntax_Syntax.Tm_app (head1,args) ->
        let uu____761 = is_constructor head1 in
        if uu____761
        then
          FStar_All.pipe_right args
            (FStar_List.for_all
               (fun uu____769  ->
                  match uu____769 with | (te,uu____773) -> is_fstar_value te))
        else false
    | FStar_Syntax_Syntax.Tm_meta (t1,_)|FStar_Syntax_Syntax.Tm_ascribed
      (t1,_,_) -> is_fstar_value t1
    | uu____799 -> false
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
    | FStar_Extraction_ML_Syntax.MLE_Record (uu____812,fields) ->
        FStar_Util.for_all
          (fun uu____824  ->
             match uu____824 with | (uu____827,e1) -> is_ml_value e1) fields
    | uu____829 -> false
let normalize_abs: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t0  ->
    let rec aux bs t copt =
      let t1 = FStar_Syntax_Subst.compress t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_abs (bs',body,copt1) ->
          aux (FStar_List.append bs bs') body copt1
      | uu____889 ->
          let e' = FStar_Syntax_Util.unascribe t1 in
          let uu____891 = FStar_Syntax_Util.is_fun e' in
          if uu____891
          then aux bs e' copt
          else FStar_Syntax_Util.abs bs e' copt in
    aux [] t0 None
let unit_binder: FStar_Syntax_Syntax.binder =
  let uu____900 =
    FStar_Syntax_Syntax.new_bv None FStar_TypeChecker_Common.t_unit in
  FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____900
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
      (let uu____944 = FStar_List.hd l in
       match uu____944 with
       | (p1,w1,e1) ->
           let uu____963 =
             let uu____968 = FStar_List.tl l in FStar_List.hd uu____968 in
           (match uu____963 with
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
                 | uu____1007 -> def)))
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
          let e1 =
            let uu____1050 = erasable g f ty in
            if uu____1050
            then
              let uu____1051 =
                type_leq g ty FStar_Extraction_ML_Syntax.ml_unit_ty in
              (if uu____1051
               then FStar_Extraction_ML_Syntax.ml_unit
               else
                 FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty)
                   (FStar_Extraction_ML_Syntax.MLE_Coerce
                      (FStar_Extraction_ML_Syntax.ml_unit,
                        FStar_Extraction_ML_Syntax.ml_unit_ty, ty)))
            else e in
          (e1, f, ty)
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
          let ty1 = eraseTypeDeep g ty in
          let uu____1067 = (type_leq_c g (Some e) ty1) expect in
          match uu____1067 with
          | (true ,Some e') -> e'
          | uu____1073 ->
              (FStar_Extraction_ML_UEnv.debug g
                 (fun uu____1078  ->
                    let uu____1079 =
                      FStar_Extraction_ML_Code.string_of_mlexpr
                        g.FStar_Extraction_ML_UEnv.currentModule e in
                    let uu____1080 =
                      FStar_Extraction_ML_Code.string_of_mlty
                        g.FStar_Extraction_ML_UEnv.currentModule ty1 in
                    let uu____1081 =
                      FStar_Extraction_ML_Code.string_of_mlty
                        g.FStar_Extraction_ML_UEnv.currentModule expect in
                    FStar_Util.print3
                      "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n"
                      uu____1079 uu____1080 uu____1081);
               FStar_All.pipe_left
                 (FStar_Extraction_ML_Syntax.with_ty expect)
                 (FStar_Extraction_ML_Syntax.MLE_Coerce (e, ty1, expect)))
let bv_as_mlty:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlty
  =
  fun g  ->
    fun bv  ->
      let uu____1088 = FStar_Extraction_ML_UEnv.lookup_bv g bv in
      match uu____1088 with
      | FStar_Util.Inl (uu____1089,t) -> t
      | uu____1097 -> FStar_Extraction_ML_Syntax.MLTY_Top
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
      let uu____1131 =
        (fun t1  ->
           match t1 with
           | FStar_Extraction_ML_Syntax.MLTY_Top  -> true
           | FStar_Extraction_ML_Syntax.MLTY_Named uu____1133 ->
               let uu____1137 = FStar_Extraction_ML_Util.udelta_unfold g t1 in
               (match uu____1137 with
                | None  -> false
                | Some t2 ->
                    (let rec is_top_ty t3 =
                       match t3 with
                       | FStar_Extraction_ML_Syntax.MLTY_Top  -> true
                       | FStar_Extraction_ML_Syntax.MLTY_Named uu____1144 ->
                           let uu____1148 =
                             FStar_Extraction_ML_Util.udelta_unfold g t3 in
                           (match uu____1148 with
                            | None  -> false
                            | Some t4 -> is_top_ty t4)
                       | uu____1151 -> false in
                     is_top_ty) t2)
           | uu____1152 -> false) mlt in
      if uu____1131
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
            g.FStar_Extraction_ML_UEnv.tcenv t0 in
        term_as_mlty' g t1
      else mlt
and term_as_mlty':
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlty
  =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Subst.compress t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_bvar _
        |FStar_Syntax_Syntax.Tm_delayed _|FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____1160 =
            let uu____1161 = FStar_Syntax_Print.term_to_string t1 in
            FStar_Util.format1 "Impossible: Unexpected term %s" uu____1161 in
          failwith uu____1160
      | FStar_Syntax_Syntax.Tm_constant uu____1162 ->
          FStar_Extraction_ML_UEnv.unknownType
      | FStar_Syntax_Syntax.Tm_uvar uu____1163 ->
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
          let uu____1226 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____1226 with
           | (bs1,c1) ->
               let uu____1231 = binders_as_ml_binders env bs1 in
               (match uu____1231 with
                | (mlbs,env1) ->
                    let t_ret =
                      let eff =
                        FStar_TypeChecker_Env.norm_eff_name
                          env1.FStar_Extraction_ML_UEnv.tcenv
                          (FStar_Syntax_Util.comp_effect_name c1) in
                      let uu____1247 =
                        let uu____1251 =
                          FStar_TypeChecker_Env.effect_decl_opt
                            env1.FStar_Extraction_ML_UEnv.tcenv eff in
                        FStar_Util.must uu____1251 in
                      match uu____1247 with
                      | (ed,qualifiers) ->
                          let uu____1263 =
                            FStar_All.pipe_right qualifiers
                              (FStar_List.contains
                                 FStar_Syntax_Syntax.Reifiable) in
                          if uu____1263
                          then
                            let t2 =
                              FStar_TypeChecker_Env.reify_comp
                                env1.FStar_Extraction_ML_UEnv.tcenv c1
                                FStar_Syntax_Syntax.U_unknown in
                            let res = term_as_mlty' env1 t2 in res
                          else
                            term_as_mlty' env1
                              (FStar_Syntax_Util.comp_result c1) in
                    let erase1 =
                      effect_as_etag env1
                        (FStar_Syntax_Util.comp_effect_name c1) in
                    let uu____1269 =
                      FStar_List.fold_right
                        (fun uu____1276  ->
                           fun uu____1277  ->
                             match (uu____1276, uu____1277) with
                             | ((uu____1288,t2),(tag,t')) ->
                                 (FStar_Extraction_ML_Syntax.E_PURE,
                                   (FStar_Extraction_ML_Syntax.MLTY_Fun
                                      (t2, tag, t')))) mlbs (erase1, t_ret) in
                    (match uu____1269 with | (uu____1296,t2) -> t2)))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let res =
            let uu____1315 =
              let uu____1316 = FStar_Syntax_Util.un_uinst head1 in
              uu____1316.FStar_Syntax_Syntax.n in
            match uu____1315 with
            | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
            | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv args
            | FStar_Syntax_Syntax.Tm_app (head2,args') ->
                let uu____1337 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app
                       (head2, (FStar_List.append args' args))) None
                    t1.FStar_Syntax_Syntax.pos in
                term_as_mlty' env uu____1337
            | uu____1353 -> FStar_Extraction_ML_UEnv.unknownType in
          res
      | FStar_Syntax_Syntax.Tm_abs (bs,ty,uu____1356) ->
          let uu____1379 = FStar_Syntax_Subst.open_term bs ty in
          (match uu____1379 with
           | (bs1,ty1) ->
               let uu____1384 = binders_as_ml_binders env bs1 in
               (match uu____1384 with | (bts,env1) -> term_as_mlty' env1 ty1))
      | FStar_Syntax_Syntax.Tm_type _
        |FStar_Syntax_Syntax.Tm_let _|FStar_Syntax_Syntax.Tm_match _ ->
          FStar_Extraction_ML_UEnv.unknownType
and arg_as_mlty:
  FStar_Extraction_ML_UEnv.env ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.aqual) ->
      FStar_Extraction_ML_Syntax.mlty
  =
  fun g  ->
    fun uu____1402  ->
      match uu____1402 with
      | (a,uu____1406) ->
          let uu____1407 = is_type g a in
          if uu____1407
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
        let uu____1412 =
          FStar_Syntax_Util.arrow_formals
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.ty in
        match uu____1412 with
        | (formals,t) ->
            let mlargs = FStar_List.map (arg_as_mlty g) args in
            let mlargs1 =
              let n_args = FStar_List.length args in
              if (FStar_List.length formals) > n_args
              then
                let uu____1456 = FStar_Util.first_N n_args formals in
                match uu____1456 with
                | (uu____1470,rest) ->
                    let uu____1484 =
                      FStar_List.map
                        (fun uu____1488  ->
                           FStar_Extraction_ML_UEnv.erasedContent) rest in
                    FStar_List.append mlargs uu____1484
              else mlargs in
            let nm =
              let uu____1493 =
                FStar_Extraction_ML_UEnv.maybe_mangle_type_projector g fv in
              match uu____1493 with
              | Some p -> p
              | None  ->
                  FStar_Extraction_ML_Syntax.mlpath_of_lident
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            FStar_Extraction_ML_Syntax.MLTY_Named (mlargs1, nm)
and binders_as_ml_binders:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.binders ->
      ((FStar_Extraction_ML_Syntax.mlident* FStar_Extraction_ML_Syntax.mlty)
        Prims.list* FStar_Extraction_ML_UEnv.env)
  =
  fun g  ->
    fun bs  ->
      let uu____1508 =
        FStar_All.pipe_right bs
          (FStar_List.fold_left
             (fun uu____1532  ->
                fun b  ->
                  match uu____1532 with
                  | (ml_bs,env) ->
                      let uu____1562 = is_type_binder g b in
                      if uu____1562
                      then
                        let b1 = Prims.fst b in
                        let env1 =
                          FStar_Extraction_ML_UEnv.extend_ty env b1
                            (Some FStar_Extraction_ML_Syntax.MLTY_Top) in
                        let ml_b =
                          let uu____1577 =
                            FStar_Extraction_ML_UEnv.bv_as_ml_termvar b1 in
                          (uu____1577, FStar_Extraction_ML_Syntax.ml_unit_ty) in
                        ((ml_b :: ml_bs), env1)
                      else
                        (let b1 = Prims.fst b in
                         let t = term_as_mlty env b1.FStar_Syntax_Syntax.sort in
                         let uu____1594 =
                           FStar_Extraction_ML_UEnv.extend_bv env b1 
                             ([], t) false false false in
                         match uu____1594 with
                         | (env1,b2) ->
                             let ml_b =
                               let uu____1612 =
                                 FStar_Extraction_ML_UEnv.removeTick b2 in
                               (uu____1612, t) in
                             ((ml_b :: ml_bs), env1))) ([], g)) in
      match uu____1508 with | (ml_bs,env) -> ((FStar_List.rev ml_bs), env)
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
      | (FStar_Extraction_ML_Syntax.MLE_Seq es1,uu____1672) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (FStar_List.append es1 [e2])
      | (uu____1674,FStar_Extraction_ML_Syntax.MLE_Seq es2) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (e1 :: es2)
      | uu____1677 -> FStar_Extraction_ML_Syntax.MLE_Seq [e1; e2]
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
                    | uu____1699 when
                        (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
                          =
                          FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr
                        -> body.FStar_Extraction_ML_Syntax.expr
                    | uu____1700 ->
                        mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def
                          body)
             | uu____1701 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body))
        | uu____1703 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body)
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
           | Some n1 -> FStar_Extraction_ML_Syntax.MLP_Tuple pats
           | uu____1717 ->
               (match q with
                | Some (FStar_Syntax_Syntax.Record_ctor (ty,fns)) ->
                    let path =
                      FStar_List.map FStar_Ident.text_of_id ty.FStar_Ident.ns in
                    let fs = record_fields fns pats in
                    FStar_Extraction_ML_Syntax.MLP_Record (path, fs)
                | uu____1733 -> p))
      | uu____1735 -> p
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
                       (fun uu____1774  ->
                          let uu____1775 =
                            FStar_Extraction_ML_Code.string_of_mlty
                              g.FStar_Extraction_ML_UEnv.currentModule t' in
                          let uu____1776 =
                            FStar_Extraction_ML_Code.string_of_mlty
                              g.FStar_Extraction_ML_UEnv.currentModule t in
                          FStar_Util.print2
                            "Expected pattern type %s; got pattern type %s\n"
                            uu____1775 uu____1776)
                   else ();
                   ok) in
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_disj uu____1785 ->
                failwith "Impossible: Nested disjunctive pattern"
            | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int
                (c,None )) ->
                let i = FStar_Const.Const_int (c, None) in
                let x = FStar_Extraction_ML_Syntax.gensym () in
                let when_clause =
                  let uu____1810 =
                    let uu____1811 =
                      let uu____1815 =
                        let uu____1817 =
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty
                               FStar_Extraction_ML_Syntax.ml_int_ty)
                            (FStar_Extraction_ML_Syntax.MLE_Var x) in
                        let uu____1818 =
                          let uu____1820 =
                            let uu____1821 =
                              let uu____1822 =
                                FStar_Extraction_ML_Util.mlconst_of_const'
                                  p.FStar_Syntax_Syntax.p i in
                              FStar_All.pipe_left
                                (fun _0_31  ->
                                   FStar_Extraction_ML_Syntax.MLE_Const _0_31)
                                uu____1822 in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.ml_int_ty)
                              uu____1821 in
                          [uu____1820] in
                        uu____1817 :: uu____1818 in
                      (FStar_Extraction_ML_Util.prims_op_equality,
                        uu____1815) in
                    FStar_Extraction_ML_Syntax.MLE_App uu____1811 in
                  FStar_All.pipe_left
                    (FStar_Extraction_ML_Syntax.with_ty
                       FStar_Extraction_ML_Syntax.ml_bool_ty) uu____1810 in
                let uu____1824 = ok FStar_Extraction_ML_Syntax.ml_int_ty in
                (g,
                  (Some
                     ((FStar_Extraction_ML_Syntax.MLP_Var x), [when_clause])),
                  uu____1824)
            | FStar_Syntax_Syntax.Pat_constant s ->
                let t =
                  FStar_TypeChecker_TcTerm.tc_constant FStar_Range.dummyRange
                    s in
                let mlty = term_as_mlty g t in
                let uu____1836 =
                  let uu____1841 =
                    let uu____1845 =
                      let uu____1846 =
                        FStar_Extraction_ML_Util.mlconst_of_const'
                          p.FStar_Syntax_Syntax.p s in
                      FStar_Extraction_ML_Syntax.MLP_Const uu____1846 in
                    (uu____1845, []) in
                  Some uu____1841 in
                let uu____1851 = ok mlty in (g, uu____1836, uu____1851)
            | FStar_Syntax_Syntax.Pat_wild x when disjunctive_pat ->
                (g, (Some (FStar_Extraction_ML_Syntax.MLP_Wild, [])), true)
            | FStar_Syntax_Syntax.Pat_var x|FStar_Syntax_Syntax.Pat_wild x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort in
                let uu____1867 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp in
                (match uu____1867 with
                 | (g1,x1) ->
                     let uu____1880 = ok mlty in
                     (g1,
                       (if imp
                        then None
                        else
                          Some ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                       uu____1880))
            | FStar_Syntax_Syntax.Pat_dot_term uu____1897 -> (g, None, true)
            | FStar_Syntax_Syntax.Pat_cons (f,pats) ->
                let uu____1921 =
                  let uu____1924 = FStar_Extraction_ML_UEnv.lookup_fv g f in
                  match uu____1924 with
                  | FStar_Util.Inr
                      (uu____1927,{
                                    FStar_Extraction_ML_Syntax.expr =
                                      FStar_Extraction_ML_Syntax.MLE_Name n1;
                                    FStar_Extraction_ML_Syntax.mlty =
                                      uu____1929;
                                    FStar_Extraction_ML_Syntax.loc =
                                      uu____1930;_},ttys,uu____1932)
                      -> (n1, ttys)
                  | uu____1939 -> failwith "Expected a constructor" in
                (match uu____1921 with
                 | (d,tys) ->
                     let nTyVars = FStar_List.length (Prims.fst tys) in
                     let uu____1953 = FStar_Util.first_N nTyVars pats in
                     (match uu____1953 with
                      | (tysVarPats,restPats) ->
                          let f_ty_opt =
                            try
                              let mlty_args =
                                FStar_All.pipe_right tysVarPats
                                  (FStar_List.map
                                     (fun uu____2027  ->
                                        match uu____2027 with
                                        | (p1,uu____2033) ->
                                            (match p1.FStar_Syntax_Syntax.v
                                             with
                                             | FStar_Syntax_Syntax.Pat_dot_term
                                                 (uu____2038,t) ->
                                                 term_as_mlty g t
                                             | uu____2044 ->
                                                 (FStar_Extraction_ML_UEnv.debug
                                                    g
                                                    (fun uu____2046  ->
                                                       let uu____2047 =
                                                         FStar_Syntax_Print.pat_to_string
                                                           p1 in
                                                       FStar_Util.print1
                                                         "Pattern %s is not extractable"
                                                         uu____2047);
                                                  Prims.raise Un_extractable)))) in
                              let f_ty =
                                FStar_Extraction_ML_Util.subst tys mlty_args in
                              let uu____2049 =
                                FStar_Extraction_ML_Util.uncurry_mlty_fun
                                  f_ty in
                              Some uu____2049
                            with | Un_extractable  -> None in
                          let uu____2064 =
                            FStar_Util.fold_map
                              (fun g1  ->
                                 fun uu____2079  ->
                                   match uu____2079 with
                                   | (p1,imp1) ->
                                       let uu____2090 =
                                         extract_one_pat disjunctive_pat true
                                           g1 p1 None in
                                       (match uu____2090 with
                                        | (g2,p2,uu____2106) -> (g2, p2))) g
                              tysVarPats in
                          (match uu____2064 with
                           | (g1,tyMLPats) ->
                               let uu____2138 =
                                 FStar_Util.fold_map
                                   (fun uu____2164  ->
                                      fun uu____2165  ->
                                        match (uu____2164, uu____2165) with
                                        | ((g2,f_ty_opt1),(p1,imp1)) ->
                                            let uu____2214 =
                                              match f_ty_opt1 with
                                              | Some (hd1::rest,res) ->
                                                  ((Some (rest, res)),
                                                    (Some hd1))
                                              | uu____2246 -> (None, None) in
                                            (match uu____2214 with
                                             | (f_ty_opt2,expected_ty) ->
                                                 let uu____2283 =
                                                   extract_one_pat
                                                     disjunctive_pat false g2
                                                     p1 expected_ty in
                                                 (match uu____2283 with
                                                  | (g3,p2,uu____2305) ->
                                                      ((g3, f_ty_opt2), p2))))
                                   (g1, f_ty_opt) restPats in
                               (match uu____2138 with
                                | ((g2,f_ty_opt1),restMLPats) ->
                                    let uu____2366 =
                                      let uu____2372 =
                                        FStar_All.pipe_right
                                          (FStar_List.append tyMLPats
                                             restMLPats)
                                          (FStar_List.collect
                                             (fun uu___141_2397  ->
                                                match uu___141_2397 with
                                                | Some x -> [x]
                                                | uu____2419 -> [])) in
                                      FStar_All.pipe_right uu____2372
                                        FStar_List.split in
                                    (match uu____2366 with
                                     | (mlPats,when_clauses) ->
                                         let pat_ty_compat =
                                           match f_ty_opt1 with
                                           | Some ([],t) -> ok t
                                           | uu____2458 -> false in
                                         let uu____2463 =
                                           let uu____2468 =
                                             let uu____2472 =
                                               resugar_pat
                                                 f.FStar_Syntax_Syntax.fv_qual
                                                 (FStar_Extraction_ML_Syntax.MLP_CTor
                                                    (d, mlPats)) in
                                             let uu____2474 =
                                               FStar_All.pipe_right
                                                 when_clauses
                                                 FStar_List.flatten in
                                             (uu____2472, uu____2474) in
                                           Some uu____2468 in
                                         (g2, uu____2463, pat_ty_compat))))))
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
        let extract_one_pat1 disj g1 p1 expected_t1 =
          let uu____2535 = extract_one_pat disj false g1 p1 expected_t1 in
          match uu____2535 with
          | (g2,Some (x,v1),b) -> (g2, (x, v1), b)
          | uu____2566 -> failwith "Impossible: Unable to translate pattern" in
        let mk_when_clause whens =
          match whens with
          | [] -> None
          | hd1::tl1 ->
              let uu____2591 =
                FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd1 tl1 in
              Some uu____2591 in
        match p.FStar_Syntax_Syntax.v with
        | FStar_Syntax_Syntax.Pat_disj [] ->
            failwith "Impossible: Empty disjunctive pattern"
        | FStar_Syntax_Syntax.Pat_disj (p1::pats) ->
            let uu____2617 = extract_one_pat1 true g p1 (Some expected_t) in
            (match uu____2617 with
             | (g',p2,b) ->
                 let uu____2640 =
                   FStar_Util.fold_map
                     (fun b1  ->
                        fun p3  ->
                          let uu____2652 =
                            extract_one_pat1 true g p3 (Some expected_t) in
                          match uu____2652 with
                          | (uu____2664,p4,b') -> ((b1 && b'), p4)) b pats in
                 (match uu____2640 with
                  | (b1,ps) ->
                      let ps1 = p2 :: ps in
                      let g1 = g' in
                      let uu____2702 =
                        FStar_All.pipe_right ps1
                          (FStar_List.partition
                             (fun uu___142_2730  ->
                                match uu___142_2730 with
                                | (uu____2734,uu____2735::uu____2736) -> true
                                | uu____2739 -> false)) in
                      (match uu____2702 with
                       | (ps_when,rest) ->
                           let ps2 =
                             FStar_All.pipe_right ps_when
                               (FStar_List.map
                                  (fun uu____2787  ->
                                     match uu____2787 with
                                     | (x,whens) ->
                                         let uu____2798 =
                                           mk_when_clause whens in
                                         (x, uu____2798))) in
                           let res =
                             match rest with
                             | [] -> (g1, ps2, b1)
                             | rest1 ->
                                 let uu____2828 =
                                   let uu____2833 =
                                     let uu____2837 =
                                       let uu____2838 =
                                         FStar_List.map Prims.fst rest1 in
                                       FStar_Extraction_ML_Syntax.MLP_Branch
                                         uu____2838 in
                                     (uu____2837, None) in
                                   uu____2833 :: ps2 in
                                 (g1, uu____2828, b1) in
                           res)))
        | uu____2852 ->
            let uu____2853 = extract_one_pat1 false g p (Some expected_t) in
            (match uu____2853 with
             | (g1,(p1,whens),b) ->
                 let when_clause = mk_when_clause whens in
                 (g1, [(p1, when_clause)], b))
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
            | FStar_Extraction_ML_Syntax.MLTY_Fun (t0,uu____2935,t1) ->
                let x = FStar_Extraction_ML_Syntax.gensym () in
                let uu____2938 =
                  let uu____2944 =
                    let uu____2949 =
                      FStar_All.pipe_left
                        (FStar_Extraction_ML_Syntax.with_ty t0)
                        (FStar_Extraction_ML_Syntax.MLE_Var x) in
                    ((x, t0), uu____2949) in
                  uu____2944 :: more_args in
                eta_args uu____2938 t1
            | FStar_Extraction_ML_Syntax.MLTY_Named (uu____2956,uu____2957)
                -> ((FStar_List.rev more_args), t)
            | uu____2969 -> failwith "Impossible: Head type is not an arrow" in
          let as_record qual1 e =
            match ((e.FStar_Extraction_ML_Syntax.expr), qual1) with
            | (FStar_Extraction_ML_Syntax.MLE_CTor (uu____2987,args),Some
               (FStar_Syntax_Syntax.Record_ctor (tyname,fields))) ->
                let path =
                  FStar_List.map FStar_Ident.text_of_id tyname.FStar_Ident.ns in
                let fields1 = record_fields fields args in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     e.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_Record (path, fields1))
            | uu____3006 -> e in
          let resugar_and_maybe_eta qual1 e =
            let uu____3019 = eta_args [] residualType in
            match uu____3019 with
            | (eargs,tres) ->
                (match eargs with
                 | [] ->
                     let uu____3047 = as_record qual1 e in
                     FStar_Extraction_ML_Util.resugar_exp uu____3047
                 | uu____3048 ->
                     let uu____3054 = FStar_List.unzip eargs in
                     (match uu____3054 with
                      | (binders,eargs1) ->
                          (match e.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_CTor (head1,args)
                               ->
                               let body =
                                 let uu____3078 =
                                   let uu____3079 =
                                     FStar_All.pipe_left
                                       (FStar_Extraction_ML_Syntax.with_ty
                                          tres)
                                       (FStar_Extraction_ML_Syntax.MLE_CTor
                                          (head1,
                                            (FStar_List.append args eargs1))) in
                                   FStar_All.pipe_left (as_record qual1)
                                     uu____3079 in
                                 FStar_All.pipe_left
                                   FStar_Extraction_ML_Util.resugar_exp
                                   uu____3078 in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    e.FStar_Extraction_ML_Syntax.mlty)
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    (binders, body))
                           | uu____3084 ->
                               failwith "Impossible: Not a constructor"))) in
          match ((mlAppExpr.FStar_Extraction_ML_Syntax.expr), qual) with
          | (uu____3086,None ) -> mlAppExpr
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____3089;
                FStar_Extraction_ML_Syntax.loc = uu____3090;_},mle::args),Some
             (FStar_Syntax_Syntax.Record_projector (constrname,f))) ->
              let f1 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append constrname.FStar_Ident.ns [f]) in
              let fn = FStar_Extraction_ML_Util.mlpath_of_lid f1 in
              let proj = FStar_Extraction_ML_Syntax.MLE_Proj (mle, fn) in
              let e =
                match args with
                | [] -> proj
                | uu____3108 ->
                    let uu____3110 =
                      let uu____3114 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj in
                      (uu____3114, args) in
                    FStar_Extraction_ML_Syntax.MLE_App uu____3110 in
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
              let uu____3129 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs)) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____3129
          | (FStar_Extraction_ML_Syntax.MLE_Name mlp,Some
             (FStar_Syntax_Syntax.Data_ctor ))
            |(FStar_Extraction_ML_Syntax.MLE_Name mlp,Some
              (FStar_Syntax_Syntax.Record_ctor _)) ->
              let uu____3135 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, [])) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____3135
          | uu____3137 -> mlAppExpr
let maybe_downgrade_eff:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.e_tag ->
      FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.e_tag
  =
  fun g  ->
    fun f  ->
      fun t  ->
        let uu____3150 =
          (f = FStar_Extraction_ML_Syntax.E_GHOST) &&
            (type_leq g t FStar_Extraction_ML_Syntax.ml_unit_ty) in
        if uu____3150 then FStar_Extraction_ML_Syntax.E_PURE else f
let rec term_as_mlexpr:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Extraction_ML_Syntax.mlexpr* FStar_Extraction_ML_Syntax.e_tag*
        FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun t  ->
      let uu____3191 = term_as_mlexpr' g t in
      match uu____3191 with
      | (e,tag,ty) ->
          let tag1 = maybe_downgrade_eff g tag ty in
          (FStar_Extraction_ML_UEnv.debug g
             (fun u  ->
                let uu____3204 =
                  let uu____3205 = FStar_Syntax_Print.tag_of_term t in
                  let uu____3206 = FStar_Syntax_Print.term_to_string t in
                  let uu____3207 =
                    FStar_Extraction_ML_Code.string_of_mlty
                      g.FStar_Extraction_ML_UEnv.currentModule ty in
                  FStar_Util.format4
                    "term_as_mlexpr (%s) :  %s has ML type %s and effect %s\n"
                    uu____3205 uu____3206 uu____3207
                    (FStar_Extraction_ML_Util.eff_to_string tag1) in
                FStar_Util.print_string uu____3204);
           erase g e ty tag1)
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
          let uu____3214 = check_term_as_mlexpr' g t f ty in
          match uu____3214 with
          | (e,t1) ->
              let uu____3221 = erase g e t1 f in
              (match uu____3221 with | (r,uu____3228,t2) -> (r, t2))
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
          let uu____3236 = term_as_mlexpr g e0 in
          match uu____3236 with
          | (e,tag,t) ->
              let tag1 = maybe_downgrade_eff g tag t in
              if FStar_Extraction_ML_Util.eff_leq tag1 f
              then let uu____3248 = maybe_coerce g e t ty in (uu____3248, ty)
              else err_unexpected_eff e0 f tag1
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
           let uu____3259 =
             let uu____3260 =
               FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos in
             let uu____3261 = FStar_Syntax_Print.tag_of_term top in
             let uu____3262 = FStar_Syntax_Print.term_to_string top in
             FStar_Util.format3 "%s: term_as_mlexpr' (%s) :  %s \n"
               uu____3260 uu____3261 uu____3262 in
           FStar_Util.print_string uu____3259);
      (let t = FStar_Syntax_Subst.compress top in
       match t.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_unknown 
         |FStar_Syntax_Syntax.Tm_delayed _
          |FStar_Syntax_Syntax.Tm_uvar _|FStar_Syntax_Syntax.Tm_bvar _ ->
           let uu____3270 =
             let uu____3271 = FStar_Syntax_Print.tag_of_term t in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____3271 in
           failwith uu____3270
       | FStar_Syntax_Syntax.Tm_type _
         |FStar_Syntax_Syntax.Tm_refine _|FStar_Syntax_Syntax.Tm_arrow _ ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Mutable_alloc ))
           ->
           let uu____3283 = term_as_mlexpr' g t1 in
           (match uu____3283 with
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
            | uu____3310 -> failwith "impossible")
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_monadic (m,uu____3319)) ->
           let t2 = FStar_Syntax_Subst.compress t1 in
           (match t2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) when
                FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname ->
                let uu____3342 =
                  let uu____3346 =
                    FStar_TypeChecker_Env.effect_decl_opt
                      g.FStar_Extraction_ML_UEnv.tcenv m in
                  FStar_Util.must uu____3346 in
                (match uu____3342 with
                 | (ed,qualifiers) ->
                     let uu____3361 =
                       let uu____3362 =
                         FStar_All.pipe_right qualifiers
                           (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
                       FStar_All.pipe_right uu____3362 Prims.op_Negation in
                     if uu____3361
                     then term_as_mlexpr' g t2
                     else
                       failwith
                         "This should not happen (should have been handled at Tm_abs level)")
            | uu____3371 -> term_as_mlexpr' g t2)
       | FStar_Syntax_Syntax.Tm_meta (t1,_)|FStar_Syntax_Syntax.Tm_uinst
         (t1,_) -> term_as_mlexpr' g t1
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____3384 =
             FStar_TypeChecker_TcTerm.type_of_tot_term
               g.FStar_Extraction_ML_UEnv.tcenv t in
           (match uu____3384 with
            | (uu____3391,ty,uu____3393) ->
                let ml_ty = term_as_mlty g ty in
                let uu____3395 =
                  let uu____3396 =
                    let uu____3397 =
                      FStar_Extraction_ML_Util.mlconst_of_const'
                        t.FStar_Syntax_Syntax.pos c in
                    FStar_All.pipe_left
                      (fun _0_32  ->
                         FStar_Extraction_ML_Syntax.MLE_Const _0_32)
                      uu____3397 in
                  FStar_Extraction_ML_Syntax.with_ty ml_ty uu____3396 in
                (uu____3395, FStar_Extraction_ML_Syntax.E_PURE, ml_ty))
       | FStar_Syntax_Syntax.Tm_name _|FStar_Syntax_Syntax.Tm_fvar _ ->
           let uu____3400 = is_type g t in
           if uu____3400
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____3405 = FStar_Extraction_ML_UEnv.lookup_term g t in
              match uu____3405 with
              | (FStar_Util.Inl uu____3412,uu____3413) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | (FStar_Util.Inr (uu____3432,x,mltys,uu____3435),qual) ->
                  (match mltys with
                   | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                       ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | ([],t1) ->
                       let uu____3460 =
                         maybe_eta_data_and_project_record g qual t1 x in
                       (uu____3460, FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | uu____3461 -> err_uninst g t mltys t))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,copt) ->
           let uu____3490 = FStar_Syntax_Subst.open_term bs body in
           (match uu____3490 with
            | (bs1,body1) ->
                let uu____3498 = binders_as_ml_binders g bs1 in
                (match uu____3498 with
                 | (ml_bs,env) ->
                     let body2 =
                       match copt with
                       | Some c ->
                           (FStar_Extraction_ML_UEnv.debug g
                              (fun uu____3528  ->
                                 match c with
                                 | FStar_Util.Inl lc ->
                                     let uu____3533 =
                                       FStar_Syntax_Print.lcomp_to_string lc in
                                     FStar_Util.print1 "Computation lc: %s\n"
                                       uu____3533
                                 | FStar_Util.Inr rc ->
                                     FStar_Util.print1 "Computation rc: %s\n"
                                       (FStar_Ident.text_of_lid
                                          (Prims.fst rc)));
                            (let uu____3542 =
                               FStar_TypeChecker_Env.is_reifiable
                                 env.FStar_Extraction_ML_UEnv.tcenv c in
                             if uu____3542
                             then
                               FStar_TypeChecker_Util.reify_body
                                 env.FStar_Extraction_ML_UEnv.tcenv body1
                             else body1))
                       | None  ->
                           (FStar_Extraction_ML_UEnv.debug g
                              (fun uu____3550  ->
                                 let uu____3551 =
                                   FStar_Syntax_Print.term_to_string body1 in
                                 FStar_Util.print1
                                   "No computation type for: %s\n" uu____3551);
                            body1) in
                     let uu____3552 = term_as_mlexpr env body2 in
                     (match uu____3552 with
                      | (ml_body,f,t1) ->
                          let uu____3562 =
                            FStar_List.fold_right
                              (fun uu____3569  ->
                                 fun uu____3570  ->
                                   match (uu____3569, uu____3570) with
                                   | ((uu____3581,targ),(f1,t2)) ->
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         (FStar_Extraction_ML_Syntax.MLTY_Fun
                                            (targ, f1, t2)))) ml_bs (f, t1) in
                          (match uu____3562 with
                           | (f1,tfun) ->
                               let uu____3594 =
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty tfun)
                                   (FStar_Extraction_ML_Syntax.MLE_Fun
                                      (ml_bs, ml_body)) in
                               (uu____3594, f1, tfun)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____3598);
              FStar_Syntax_Syntax.tk = uu____3599;
              FStar_Syntax_Syntax.pos = uu____3600;
              FStar_Syntax_Syntax.vars = uu____3601;_},uu____3602)
           -> failwith "Unreachable? Tm_app Const_reflect"
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let is_total uu___144_3644 =
             match uu___144_3644 with
             | FStar_Util.Inl l -> FStar_Syntax_Util.is_total_lcomp l
             | FStar_Util.Inr (l,flags) ->
                 (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid)
                   ||
                   (FStar_All.pipe_right flags
                      (FStar_List.existsb
                         (fun uu___143_3662  ->
                            match uu___143_3662 with
                            | FStar_Syntax_Syntax.TOTAL  -> true
                            | uu____3663 -> false))) in
           let uu____3664 =
             let uu____3667 =
               let uu____3668 = FStar_Syntax_Subst.compress head1 in
               uu____3668.FStar_Syntax_Syntax.n in
             ((head1.FStar_Syntax_Syntax.n), uu____3667) in
           (match uu____3664 with
            | (FStar_Syntax_Syntax.Tm_uvar uu____3674,uu____3675) ->
                let t1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.Iota;
                    FStar_TypeChecker_Normalize.Zeta;
                    FStar_TypeChecker_Normalize.EraseUniverses;
                    FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                    g.FStar_Extraction_ML_UEnv.tcenv t in
                term_as_mlexpr' g t1
            | (uu____3685,FStar_Syntax_Syntax.Tm_abs (bs,uu____3687,Some lc))
                when is_total lc ->
                let t1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.Iota;
                    FStar_TypeChecker_Normalize.Zeta;
                    FStar_TypeChecker_Normalize.EraseUniverses;
                    FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                    g.FStar_Extraction_ML_UEnv.tcenv t in
                term_as_mlexpr' g t1
            | (uu____3716,FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_reify )) ->
                let e =
                  let uu____3718 = FStar_List.hd args in
                  FStar_TypeChecker_Util.reify_body_with_arg
                    g.FStar_Extraction_ML_UEnv.tcenv head1 uu____3718 in
                let tm =
                  let uu____3726 =
                    let uu____3727 = FStar_TypeChecker_Util.remove_reify e in
                    let uu____3728 = FStar_List.tl args in
                    FStar_Syntax_Syntax.mk_Tm_app uu____3727 uu____3728 in
                  uu____3726 None t.FStar_Syntax_Syntax.pos in
                term_as_mlexpr' g tm
            | uu____3737 ->
                let rec extract_app is_data uu____3765 uu____3766 restArgs =
                  match (uu____3765, uu____3766) with
                  | ((mlhead,mlargs_f),(f,t1)) ->
                      (match (restArgs, t1) with
                       | ([],uu____3814) ->
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
                                | uu____3828 -> false) in
                           let uu____3829 =
                             if evaluation_order_guaranteed
                             then
                               let uu____3842 =
                                 FStar_All.pipe_right
                                   (FStar_List.rev mlargs_f)
                                   (FStar_List.map Prims.fst) in
                               ([], uu____3842)
                             else
                               FStar_List.fold_left
                                 (fun uu____3867  ->
                                    fun uu____3868  ->
                                      match (uu____3867, uu____3868) with
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
                                                 () in
                                             let uu____3923 =
                                               let uu____3925 =
                                                 FStar_All.pipe_left
                                                   (FStar_Extraction_ML_Syntax.with_ty
                                                      arg.FStar_Extraction_ML_Syntax.mlty)
                                                   (FStar_Extraction_ML_Syntax.MLE_Var
                                                      x) in
                                               uu____3925 :: out_args in
                                             (((x, arg) :: lbs), uu____3923)))
                                 ([], []) mlargs_f in
                           (match uu____3829 with
                            | (lbs,mlargs) ->
                                let app =
                                  let uu____3952 =
                                    FStar_All.pipe_left
                                      (FStar_Extraction_ML_Syntax.with_ty t1)
                                      (FStar_Extraction_ML_Syntax.MLE_App
                                         (mlhead, mlargs)) in
                                  FStar_All.pipe_left
                                    (maybe_eta_data_and_project_record g
                                       is_data t1) uu____3952 in
                                let l_app =
                                  FStar_List.fold_right
                                    (fun uu____3957  ->
                                       fun out  ->
                                         match uu____3957 with
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
                                (l_app, f, t1))
                       | ((arg,uu____3970)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                          (formal_t,f',t2)) when
                           (is_type g arg) &&
                             (type_leq g formal_t
                                FStar_Extraction_ML_Syntax.ml_unit_ty)
                           ->
                           let uu____3988 =
                             let uu____3991 =
                               FStar_Extraction_ML_Util.join
                                 arg.FStar_Syntax_Syntax.pos f f' in
                             (uu____3991, t2) in
                           extract_app is_data
                             (mlhead,
                               ((FStar_Extraction_ML_Syntax.ml_unit,
                                  FStar_Extraction_ML_Syntax.E_PURE) ::
                               mlargs_f)) uu____3988 rest
                       | ((e0,uu____3998)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                          (tExpected,f',t2)) ->
                           let r = e0.FStar_Syntax_Syntax.pos in
                           let uu____4017 = term_as_mlexpr g e0 in
                           (match uu____4017 with
                            | (e01,f0,tInferred) ->
                                let e02 =
                                  maybe_coerce g e01 tInferred tExpected in
                                let uu____4028 =
                                  let uu____4031 =
                                    FStar_Extraction_ML_Util.join_l r
                                      [f; f'; f0] in
                                  (uu____4031, t2) in
                                extract_app is_data
                                  (mlhead, ((e02, f0) :: mlargs_f))
                                  uu____4028 rest)
                       | uu____4037 ->
                           let uu____4044 =
                             FStar_Extraction_ML_Util.udelta_unfold g t1 in
                           (match uu____4044 with
                            | Some t2 ->
                                extract_app is_data (mlhead, mlargs_f)
                                  (f, t2) restArgs
                            | None  ->
                                err_ill_typed_application g top restArgs t1)) in
                let extract_app_maybe_projector is_data mlhead uu____4080
                  args1 =
                  match uu____4080 with
                  | (f,t1) ->
                      (match is_data with
                       | Some (FStar_Syntax_Syntax.Record_projector
                           uu____4099) ->
                           let rec remove_implicits args2 f1 t2 =
                             match (args2, t2) with
                             | ((a0,Some (FStar_Syntax_Syntax.Implicit
                                 uu____4149))::args3,FStar_Extraction_ML_Syntax.MLTY_Fun
                                (uu____4151,f',t3)) ->
                                 let uu____4176 =
                                   FStar_Extraction_ML_Util.join
                                     a0.FStar_Syntax_Syntax.pos f1 f' in
                                 remove_implicits args3 uu____4176 t3
                             | uu____4177 -> (args2, f1, t2) in
                           let uu____4192 = remove_implicits args1 f t1 in
                           (match uu____4192 with
                            | (args2,f1,t2) ->
                                extract_app is_data (mlhead, []) (f1, t2)
                                  args2)
                       | uu____4225 ->
                           extract_app is_data (mlhead, []) (f, t1) args1) in
                let uu____4232 = is_type g t in
                if uu____4232
                then
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
                else
                  (let head2 = FStar_Syntax_Util.un_uinst head1 in
                   match head2.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_name _
                     |FStar_Syntax_Syntax.Tm_fvar _ ->
                       let uu____4243 =
                         let uu____4250 =
                           FStar_Extraction_ML_UEnv.lookup_term g head2 in
                         match uu____4250 with
                         | (FStar_Util.Inr (uu____4260,x1,x2,x3),q) ->
                             ((x1, x2, x3), q)
                         | uu____4285 -> failwith "FIXME Ty" in
                       (match uu____4243 with
                        | ((head_ml,(vars,t1),inst_ok),qual) ->
                            let has_typ_apps =
                              match args with
                              | (a,uu____4314)::uu____4315 -> is_type g a
                              | uu____4329 -> false in
                            let uu____4335 =
                              match vars with
                              | uu____4352::uu____4353 when
                                  (Prims.op_Negation has_typ_apps) && inst_ok
                                  -> (head_ml, t1, args)
                              | uu____4360 ->
                                  let n1 = FStar_List.length vars in
                                  if n1 <= (FStar_List.length args)
                                  then
                                    let uu____4380 =
                                      FStar_Util.first_N n1 args in
                                    (match uu____4380 with
                                     | (prefix1,rest) ->
                                         let prefixAsMLTypes =
                                           FStar_List.map
                                             (fun uu____4433  ->
                                                match uu____4433 with
                                                | (x,uu____4437) ->
                                                    term_as_mlty g x) prefix1 in
                                         let t2 =
                                           instantiate (vars, t1)
                                             prefixAsMLTypes in
                                         let head3 =
                                           match head_ml.FStar_Extraction_ML_Syntax.expr
                                           with
                                           | FStar_Extraction_ML_Syntax.MLE_Name
                                             _
                                             |FStar_Extraction_ML_Syntax.MLE_Var
                                             _ ->
                                               let uu___148_4442 = head_ml in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (uu___148_4442.FStar_Extraction_ML_Syntax.expr);
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   = t2;
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___148_4442.FStar_Extraction_ML_Syntax.loc)
                                               }
                                           | FStar_Extraction_ML_Syntax.MLE_App
                                               (head3,{
                                                        FStar_Extraction_ML_Syntax.expr
                                                          =
                                                          FStar_Extraction_ML_Syntax.MLE_Const
                                                          (FStar_Extraction_ML_Syntax.MLC_Unit
                                                          );
                                                        FStar_Extraction_ML_Syntax.mlty
                                                          = uu____4444;
                                                        FStar_Extraction_ML_Syntax.loc
                                                          = uu____4445;_}::[])
                                               ->
                                               FStar_All.pipe_right
                                                 (FStar_Extraction_ML_Syntax.MLE_App
                                                    ((let uu___149_4448 =
                                                        head3 in
                                                      {
                                                        FStar_Extraction_ML_Syntax.expr
                                                          =
                                                          (uu___149_4448.FStar_Extraction_ML_Syntax.expr);
                                                        FStar_Extraction_ML_Syntax.mlty
                                                          =
                                                          (FStar_Extraction_ML_Syntax.MLTY_Fun
                                                             (FStar_Extraction_ML_Syntax.ml_unit_ty,
                                                               FStar_Extraction_ML_Syntax.E_PURE,
                                                               t2));
                                                        FStar_Extraction_ML_Syntax.loc
                                                          =
                                                          (uu___149_4448.FStar_Extraction_ML_Syntax.loc)
                                                      }),
                                                      [FStar_Extraction_ML_Syntax.ml_unit]))
                                                 (FStar_Extraction_ML_Syntax.with_ty
                                                    t2)
                                           | uu____4449 ->
                                               failwith
                                                 "Impossible: Unexpected head term" in
                                         (head3, t2, rest))
                                  else err_uninst g head2 (vars, t1) top in
                            (match uu____4335 with
                             | (head_ml1,head_t,args1) ->
                                 (match args1 with
                                  | [] ->
                                      let uu____4487 =
                                        maybe_eta_data_and_project_record g
                                          qual head_t head_ml1 in
                                      (uu____4487,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        head_t)
                                  | uu____4488 ->
                                      extract_app_maybe_projector qual
                                        head_ml1
                                        (FStar_Extraction_ML_Syntax.E_PURE,
                                          head_t) args1)))
                   | uu____4494 ->
                       let uu____4495 = term_as_mlexpr g head2 in
                       (match uu____4495 with
                        | (head3,f,t1) ->
                            extract_app_maybe_projector None head3 (f, t1)
                              args)))
       | FStar_Syntax_Syntax.Tm_ascribed (e0,(tc,uu____4507),f) ->
           let t1 =
             match tc with
             | FStar_Util.Inl t1 -> term_as_mlty g t1
             | FStar_Util.Inr c ->
                 term_as_mlty g (FStar_Syntax_Util.comp_result c) in
           let f1 =
             match f with
             | None  -> failwith "Ascription node with an empty effect label"
             | Some l -> effect_as_etag g l in
           let uu____4561 = check_term_as_mlexpr g e0 f1 t1 in
           (match uu____4561 with | (e,t2) -> (e, f1, t2))
       | FStar_Syntax_Syntax.Tm_let ((is_rec,lbs),e') ->
           let top_level = FStar_Syntax_Syntax.is_top_level lbs in
           let uu____4582 =
             if is_rec
             then FStar_Syntax_Subst.open_let_rec lbs e'
             else
               (let uu____4590 = FStar_Syntax_Syntax.is_top_level lbs in
                if uu____4590
                then (lbs, e')
                else
                  (let lb = FStar_List.hd lbs in
                   let x =
                     let uu____4600 =
                       FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                     FStar_Syntax_Syntax.freshen_bv uu____4600 in
                   let lb1 =
                     let uu___150_4602 = lb in
                     {
                       FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                       FStar_Syntax_Syntax.lbunivs =
                         (uu___150_4602.FStar_Syntax_Syntax.lbunivs);
                       FStar_Syntax_Syntax.lbtyp =
                         (uu___150_4602.FStar_Syntax_Syntax.lbtyp);
                       FStar_Syntax_Syntax.lbeff =
                         (uu___150_4602.FStar_Syntax_Syntax.lbeff);
                       FStar_Syntax_Syntax.lbdef =
                         (uu___150_4602.FStar_Syntax_Syntax.lbdef)
                     } in
                   let e'1 =
                     FStar_Syntax_Subst.subst
                       [FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x)] e' in
                   ([lb1], e'1))) in
           (match uu____4582 with
            | (lbs1,e'1) ->
                let lbs2 =
                  if top_level
                  then
                    FStar_All.pipe_right lbs1
                      (FStar_List.map
                         (fun lb  ->
                            let tcenv =
                              let uu____4619 =
                                FStar_Ident.lid_of_path
                                  (FStar_List.append
                                     (Prims.fst
                                        g.FStar_Extraction_ML_UEnv.currentModule)
                                     [Prims.snd
                                        g.FStar_Extraction_ML_UEnv.currentModule])
                                  FStar_Range.dummyRange in
                              FStar_TypeChecker_Env.set_current_module
                                g.FStar_Extraction_ML_UEnv.tcenv uu____4619 in
                            FStar_Extraction_ML_UEnv.debug g
                              (fun uu____4623  ->
                                 FStar_Options.set_option "debug_level"
                                   (FStar_Options.List
                                      [FStar_Options.String "Norm";
                                      FStar_Options.String "Extraction"]));
                            (let lbdef =
                               let uu____4627 = FStar_Options.ml_ish () in
                               if uu____4627
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
                             let uu___151_4631 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___151_4631.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___151_4631.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___151_4631.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___151_4631.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef
                             })))
                  else lbs1 in
                let maybe_generalize uu____4645 =
                  match uu____4645 with
                  | { FStar_Syntax_Syntax.lbname = lbname_;
                      FStar_Syntax_Syntax.lbunivs = uu____4656;
                      FStar_Syntax_Syntax.lbtyp = t1;
                      FStar_Syntax_Syntax.lbeff = lbeff;
                      FStar_Syntax_Syntax.lbdef = e;_} ->
                      let f_e = effect_as_etag g lbeff in
                      let t2 = FStar_Syntax_Subst.compress t1 in
                      (match t2.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                           let uu____4699 = FStar_List.hd bs in
                           FStar_All.pipe_right uu____4699 (is_type_binder g)
                           ->
                           let uu____4706 = FStar_Syntax_Subst.open_comp bs c in
                           (match uu____4706 with
                            | (bs1,c1) ->
                                let uu____4720 =
                                  let uu____4725 =
                                    FStar_Util.prefix_until
                                      (fun x  ->
                                         let uu____4743 = is_type_binder g x in
                                         Prims.op_Negation uu____4743) bs1 in
                                  match uu____4725 with
                                  | None  ->
                                      (bs1,
                                        (FStar_Syntax_Util.comp_result c1))
                                  | Some (bs2,b,rest) ->
                                      let uu____4791 =
                                        FStar_Syntax_Util.arrow (b :: rest)
                                          c1 in
                                      (bs2, uu____4791) in
                                (match uu____4720 with
                                 | (tbinders,tbody) ->
                                     let n_tbinders =
                                       FStar_List.length tbinders in
                                     let e1 =
                                       let uu____4821 = normalize_abs e in
                                       FStar_All.pipe_right uu____4821
                                         FStar_Syntax_Util.unmeta in
                                     (match e1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Tm_abs
                                          (bs2,body,copt) ->
                                          let uu____4856 =
                                            FStar_Syntax_Subst.open_term bs2
                                              body in
                                          (match uu____4856 with
                                           | (bs3,body1) ->
                                               if
                                                 n_tbinders <=
                                                   (FStar_List.length bs3)
                                               then
                                                 let uu____4886 =
                                                   FStar_Util.first_N
                                                     n_tbinders bs3 in
                                                 (match uu____4886 with
                                                  | (targs,rest_args) ->
                                                      let expected_source_ty
                                                        =
                                                        let s =
                                                          FStar_List.map2
                                                            (fun uu____4929 
                                                               ->
                                                               fun uu____4930
                                                                  ->
                                                                 match 
                                                                   (uu____4929,
                                                                    uu____4930)
                                                                 with
                                                                 | ((x,uu____4940),
                                                                    (y,uu____4942))
                                                                    ->
                                                                    let uu____4947
                                                                    =
                                                                    let uu____4952
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    y in
                                                                    (x,
                                                                    uu____4952) in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____4947)
                                                            tbinders targs in
                                                        FStar_Syntax_Subst.subst
                                                          s tbody in
                                                      let env =
                                                        FStar_List.fold_left
                                                          (fun env  ->
                                                             fun uu____4957 
                                                               ->
                                                               match uu____4957
                                                               with
                                                               | (a,uu____4961)
                                                                   ->
                                                                   FStar_Extraction_ML_UEnv.extend_ty
                                                                    env a
                                                                    None) g
                                                          targs in
                                                      let expected_t =
                                                        term_as_mlty env
                                                          expected_source_ty in
                                                      let polytype =
                                                        let uu____4969 =
                                                          FStar_All.pipe_right
                                                            targs
                                                            (FStar_List.map
                                                               (fun
                                                                  uu____4983 
                                                                  ->
                                                                  match uu____4983
                                                                  with
                                                                  | (x,uu____4989)
                                                                    ->
                                                                    FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                                    x)) in
                                                        (uu____4969,
                                                          expected_t) in
                                                      let add_unit =
                                                        match rest_args with
                                                        | [] ->
                                                            let uu____4996 =
                                                              is_fstar_value
                                                                body1 in
                                                            Prims.op_Negation
                                                              uu____4996
                                                        | uu____4997 -> false in
                                                      let rest_args1 =
                                                        if add_unit
                                                        then unit_binder ::
                                                          rest_args
                                                        else rest_args in
                                                      let body2 =
                                                        match rest_args1 with
                                                        | [] -> body1
                                                        | uu____5006 ->
                                                            FStar_Syntax_Util.abs
                                                              rest_args1
                                                              body1 copt in
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
                                                 fun uu____5057  ->
                                                   match uu____5057 with
                                                   | (a,uu____5061) ->
                                                       FStar_Extraction_ML_UEnv.extend_ty
                                                         env a None) g
                                              tbinders in
                                          let expected_t =
                                            term_as_mlty env tbody in
                                          let polytype =
                                            let uu____5069 =
                                              FStar_All.pipe_right tbinders
                                                (FStar_List.map
                                                   (fun uu____5080  ->
                                                      match uu____5080 with
                                                      | (x,uu____5086) ->
                                                          FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                            x)) in
                                            (uu____5069, expected_t) in
                                          let args =
                                            FStar_All.pipe_right tbinders
                                              (FStar_List.map
                                                 (fun uu____5095  ->
                                                    match uu____5095 with
                                                    | (bv,uu____5099) ->
                                                        let uu____5100 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            bv in
                                                        FStar_All.pipe_right
                                                          uu____5100
                                                          FStar_Syntax_Syntax.as_arg)) in
                                          let e2 =
                                            (FStar_Syntax_Syntax.mk
                                               (FStar_Syntax_Syntax.Tm_app
                                                  (e1, args))) None
                                              e1.FStar_Syntax_Syntax.pos in
                                          (lbname_, f_e,
                                            (t2, (tbinders, polytype)),
                                            false, e2)
                                      | uu____5138 ->
                                          err_value_restriction e1)))
                       | uu____5148 ->
                           let expected_t = term_as_mlty g t2 in
                           (lbname_, f_e, (t2, ([], ([], expected_t))),
                             false, e)) in
                let check_lb env uu____5205 =
                  match uu____5205 with
                  | (nm,(lbname,f,(t1,(targs,polytype)),add_unit,e)) ->
                      let env1 =
                        FStar_List.fold_left
                          (fun env1  ->
                             fun uu____5276  ->
                               match uu____5276 with
                               | (a,uu____5280) ->
                                   FStar_Extraction_ML_UEnv.extend_ty env1 a
                                     None) env targs in
                      let expected_t =
                        if add_unit
                        then
                          FStar_Extraction_ML_Syntax.MLTY_Fun
                            (FStar_Extraction_ML_Syntax.ml_unit_ty,
                              FStar_Extraction_ML_Syntax.E_PURE,
                              (Prims.snd polytype))
                        else Prims.snd polytype in
                      let uu____5283 =
                        check_term_as_mlexpr env1 e f expected_t in
                      (match uu____5283 with
                       | (e1,uu____5289) ->
                           let f1 = maybe_downgrade_eff env1 f expected_t in
                           (f1,
                             {
                               FStar_Extraction_ML_Syntax.mllb_name = nm;
                               FStar_Extraction_ML_Syntax.mllb_tysc =
                                 (Some polytype);
                               FStar_Extraction_ML_Syntax.mllb_add_unit =
                                 add_unit;
                               FStar_Extraction_ML_Syntax.mllb_def = e1;
                               FStar_Extraction_ML_Syntax.print_typ = true
                             })) in
                let lbs3 =
                  FStar_All.pipe_right lbs2 (FStar_List.map maybe_generalize) in
                let uu____5324 =
                  FStar_List.fold_right
                    (fun lb  ->
                       fun uu____5363  ->
                         match uu____5363 with
                         | (env,lbs4) ->
                             let uu____5427 = lb in
                             (match uu____5427 with
                              | (lbname,uu____5452,(t1,(uu____5454,polytype)),add_unit,uu____5457)
                                  ->
                                  let uu____5464 =
                                    FStar_Extraction_ML_UEnv.extend_lb env
                                      lbname t1 polytype add_unit true in
                                  (match uu____5464 with
                                   | (env1,nm) -> (env1, ((nm, lb) :: lbs4)))))
                    lbs3 (g, []) in
                (match uu____5324 with
                 | (env_body,lbs4) ->
                     let env_def = if is_rec then env_body else g in
                     let lbs5 =
                       FStar_All.pipe_right lbs4
                         (FStar_List.map (check_lb env_def)) in
                     let e'_rng = e'1.FStar_Syntax_Syntax.pos in
                     let uu____5607 = term_as_mlexpr env_body e'1 in
                     (match uu____5607 with
                      | (e'2,f',t') ->
                          let f =
                            let uu____5618 =
                              let uu____5620 = FStar_List.map Prims.fst lbs5 in
                              f' :: uu____5620 in
                            FStar_Extraction_ML_Util.join_l e'_rng uu____5618 in
                          let is_rec1 =
                            if is_rec = true
                            then FStar_Extraction_ML_Syntax.Rec
                            else FStar_Extraction_ML_Syntax.NonRec in
                          let uu____5626 =
                            let uu____5627 =
                              let uu____5628 =
                                let uu____5629 =
                                  FStar_List.map Prims.snd lbs5 in
                                (is_rec1, [], uu____5629) in
                              mk_MLE_Let top_level uu____5628 e'2 in
                            let uu____5635 =
                              FStar_Extraction_ML_Util.mlloc_of_range
                                t.FStar_Syntax_Syntax.pos in
                            FStar_Extraction_ML_Syntax.with_ty_loc t'
                              uu____5627 uu____5635 in
                          (uu____5626, f, t'))))
       | FStar_Syntax_Syntax.Tm_match (scrutinee,pats) ->
           let uu____5664 = term_as_mlexpr g scrutinee in
           (match uu____5664 with
            | (e,f_e,t_e) ->
                let uu____5674 = check_pats_for_ite pats in
                (match uu____5674 with
                 | (b,then_e,else_e) ->
                     let no_lift x t1 = x in
                     if b
                     then
                       (match (then_e, else_e) with
                        | (Some then_e1,Some else_e1) ->
                            let uu____5709 = term_as_mlexpr g then_e1 in
                            (match uu____5709 with
                             | (then_mle,f_then,t_then) ->
                                 let uu____5719 = term_as_mlexpr g else_e1 in
                                 (match uu____5719 with
                                  | (else_mle,f_else,t_else) ->
                                      let uu____5729 =
                                        let uu____5736 =
                                          type_leq g t_then t_else in
                                        if uu____5736
                                        then (t_else, no_lift)
                                        else
                                          (let uu____5748 =
                                             type_leq g t_else t_then in
                                           if uu____5748
                                           then (t_then, no_lift)
                                           else
                                             (FStar_Extraction_ML_Syntax.MLTY_Top,
                                               FStar_Extraction_ML_Syntax.apply_obj_repr)) in
                                      (match uu____5729 with
                                       | (t_branch,maybe_lift1) ->
                                           let uu____5777 =
                                             let uu____5778 =
                                               let uu____5779 =
                                                 let uu____5784 =
                                                   maybe_lift1 then_mle
                                                     t_then in
                                                 let uu____5785 =
                                                   let uu____5787 =
                                                     maybe_lift1 else_mle
                                                       t_else in
                                                   Some uu____5787 in
                                                 (e, uu____5784, uu____5785) in
                                               FStar_Extraction_ML_Syntax.MLE_If
                                                 uu____5779 in
                                             FStar_All.pipe_left
                                               (FStar_Extraction_ML_Syntax.with_ty
                                                  t_branch) uu____5778 in
                                           let uu____5789 =
                                             FStar_Extraction_ML_Util.join
                                               then_e1.FStar_Syntax_Syntax.pos
                                               f_then f_else in
                                           (uu____5777, uu____5789, t_branch))))
                        | uu____5790 ->
                            failwith
                              "ITE pats matched but then and else expressions not found?")
                     else
                       (let uu____5799 =
                          FStar_All.pipe_right pats
                            (FStar_Util.fold_map
                               (fun compat  ->
                                  fun br  ->
                                    let uu____5849 =
                                      FStar_Syntax_Subst.open_branch br in
                                    match uu____5849 with
                                    | (pat,when_opt,branch1) ->
                                        let uu____5879 =
                                          extract_pat g pat t_e in
                                        (match uu____5879 with
                                         | (env,p,pat_t_compat) ->
                                             let uu____5910 =
                                               match when_opt with
                                               | None  ->
                                                   (None,
                                                     FStar_Extraction_ML_Syntax.E_PURE)
                                               | Some w ->
                                                   let uu____5925 =
                                                     term_as_mlexpr env w in
                                                   (match uu____5925 with
                                                    | (w1,f_w,t_w) ->
                                                        let w2 =
                                                          maybe_coerce env w1
                                                            t_w
                                                            FStar_Extraction_ML_Syntax.ml_bool_ty in
                                                        ((Some w2), f_w)) in
                                             (match uu____5910 with
                                              | (when_opt1,f_when) ->
                                                  let uu____5953 =
                                                    term_as_mlexpr env
                                                      branch1 in
                                                  (match uu____5953 with
                                                   | (mlbranch,f_branch,t_branch)
                                                       ->
                                                       let uu____5972 =
                                                         FStar_All.pipe_right
                                                           p
                                                           (FStar_List.map
                                                              (fun uu____6009
                                                                  ->
                                                                 match uu____6009
                                                                 with
                                                                 | (p1,wopt)
                                                                    ->
                                                                    let when_clause
                                                                    =
                                                                    FStar_Extraction_ML_Util.conjoin_opt
                                                                    wopt
                                                                    when_opt1 in
                                                                    (p1,
                                                                    (when_clause,
                                                                    f_when),
                                                                    (mlbranch,
                                                                    f_branch,
                                                                    t_branch)))) in
                                                       ((compat &&
                                                           pat_t_compat),
                                                         uu____5972))))) true) in
                        match uu____5799 with
                        | (pat_t_compat,mlbranches) ->
                            let mlbranches1 = FStar_List.flatten mlbranches in
                            let e1 =
                              if pat_t_compat
                              then e
                              else
                                (FStar_Extraction_ML_UEnv.debug g
                                   (fun uu____6095  ->
                                      let uu____6096 =
                                        FStar_Extraction_ML_Code.string_of_mlexpr
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          e in
                                      let uu____6097 =
                                        FStar_Extraction_ML_Code.string_of_mlty
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          t_e in
                                      FStar_Util.print2
                                        "Coercing scrutinee %s from type %s because pattern type is incompatible\n"
                                        uu____6096 uu____6097);
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty t_e)
                                   (FStar_Extraction_ML_Syntax.MLE_Coerce
                                      (e, t_e,
                                        FStar_Extraction_ML_Syntax.MLTY_Top))) in
                            (match mlbranches1 with
                             | [] ->
                                 let uu____6110 =
                                   let uu____6115 =
                                     let uu____6124 =
                                       FStar_Syntax_Syntax.lid_as_fv
                                         FStar_Syntax_Const.failwith_lid
                                         FStar_Syntax_Syntax.Delta_constant
                                         None in
                                     FStar_Extraction_ML_UEnv.lookup_fv g
                                       uu____6124 in
                                   FStar_All.pipe_left FStar_Util.right
                                     uu____6115 in
                                 (match uu____6110 with
                                  | (uu____6146,fw,uu____6148,uu____6149) ->
                                      let uu____6150 =
                                        let uu____6151 =
                                          let uu____6152 =
                                            let uu____6156 =
                                              let uu____6158 =
                                                FStar_All.pipe_left
                                                  (FStar_Extraction_ML_Syntax.with_ty
                                                     FStar_Extraction_ML_Syntax.ml_string_ty)
                                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                                     (FStar_Extraction_ML_Syntax.MLC_String
                                                        "unreachable")) in
                                              [uu____6158] in
                                            (fw, uu____6156) in
                                          FStar_Extraction_ML_Syntax.MLE_App
                                            uu____6152 in
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             FStar_Extraction_ML_Syntax.ml_unit_ty)
                                          uu____6151 in
                                      (uu____6150,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        FStar_Extraction_ML_Syntax.ml_unit_ty))
                             | (uu____6160,uu____6161,(uu____6162,f_first,t_first))::rest
                                 ->
                                 let uu____6194 =
                                   FStar_List.fold_left
                                     (fun uu____6210  ->
                                        fun uu____6211  ->
                                          match (uu____6210, uu____6211) with
                                          | ((topt,f),(uu____6241,uu____6242,
                                                       (uu____6243,f_branch,t_branch)))
                                              ->
                                              let f1 =
                                                FStar_Extraction_ML_Util.join
                                                  top.FStar_Syntax_Syntax.pos
                                                  f f_branch in
                                              let topt1 =
                                                match topt with
                                                | None  -> None
                                                | Some t1 ->
                                                    let uu____6274 =
                                                      type_leq g t1 t_branch in
                                                    if uu____6274
                                                    then Some t_branch
                                                    else
                                                      (let uu____6277 =
                                                         type_leq g t_branch
                                                           t1 in
                                                       if uu____6277
                                                       then Some t1
                                                       else None) in
                                              (topt1, f1))
                                     ((Some t_first), f_first) rest in
                                 (match uu____6194 with
                                  | (topt,f_match) ->
                                      let mlbranches2 =
                                        FStar_All.pipe_right mlbranches1
                                          (FStar_List.map
                                             (fun uu____6323  ->
                                                match uu____6323 with
                                                | (p,(wopt,uu____6339),
                                                   (b1,uu____6341,t1)) ->
                                                    let b2 =
                                                      match topt with
                                                      | None  ->
                                                          FStar_Extraction_ML_Syntax.apply_obj_repr
                                                            b1 t1
                                                      | Some uu____6352 -> b1 in
                                                    (p, wopt, b2))) in
                                      let t_match =
                                        match topt with
                                        | None  ->
                                            FStar_Extraction_ML_Syntax.MLTY_Top
                                        | Some t1 -> t1 in
                                      let uu____6356 =
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             t_match)
                                          (FStar_Extraction_ML_Syntax.MLE_Match
                                             (e1, mlbranches2)) in
                                      (uu____6356, f_match, t_match)))))))
let fresh: Prims.string -> (Prims.string* Prims.int) =
  let c = FStar_Util.mk_ref (Prims.parse_int "0") in
  fun x  ->
    FStar_Util.incr c; (let uu____6374 = FStar_ST.read c in (x, uu____6374))
let ind_discriminator_body:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlmodule1
  =
  fun env  ->
    fun discName  ->
      fun constrName  ->
        let uu____6386 =
          let uu____6389 =
            FStar_TypeChecker_Env.lookup_lid
              env.FStar_Extraction_ML_UEnv.tcenv discName in
          FStar_All.pipe_left Prims.fst uu____6389 in
        match uu____6386 with
        | (uu____6402,fstar_disc_type) ->
            let wildcards =
              let uu____6410 =
                let uu____6411 = FStar_Syntax_Subst.compress fstar_disc_type in
                uu____6411.FStar_Syntax_Syntax.n in
              match uu____6410 with
              | FStar_Syntax_Syntax.Tm_arrow (binders,uu____6420) ->
                  let uu____6431 =
                    FStar_All.pipe_right binders
                      (FStar_List.filter
                         (fun uu___145_6446  ->
                            match uu___145_6446 with
                            | (uu____6450,Some (FStar_Syntax_Syntax.Implicit
                               uu____6451)) -> true
                            | uu____6453 -> false)) in
                  FStar_All.pipe_right uu____6431
                    (FStar_List.map
                       (fun uu____6473  ->
                          let uu____6477 = fresh "_" in
                          (uu____6477, FStar_Extraction_ML_Syntax.MLTY_Top)))
              | uu____6482 -> failwith "Discriminator must be a function" in
            let mlid = fresh "_discr_" in
            let targ = FStar_Extraction_ML_Syntax.MLTY_Top in
            let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top in
            let discrBody =
              let uu____6494 =
                let uu____6495 =
                  let uu____6501 =
                    let uu____6502 =
                      let uu____6503 =
                        let uu____6511 =
                          let uu____6512 =
                            let uu____6513 =
                              let uu____6514 =
                                FStar_Extraction_ML_Syntax.idsym mlid in
                              ([], uu____6514) in
                            FStar_Extraction_ML_Syntax.MLE_Name uu____6513 in
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty targ)
                            uu____6512 in
                        let uu____6516 =
                          let uu____6522 =
                            let uu____6527 =
                              let uu____6528 =
                                let uu____6532 =
                                  FStar_Extraction_ML_Syntax.mlpath_of_lident
                                    constrName in
                                (uu____6532,
                                  [FStar_Extraction_ML_Syntax.MLP_Wild]) in
                              FStar_Extraction_ML_Syntax.MLP_CTor uu____6528 in
                            let uu____6534 =
                              FStar_All.pipe_left
                                (FStar_Extraction_ML_Syntax.with_ty
                                   FStar_Extraction_ML_Syntax.ml_bool_ty)
                                (FStar_Extraction_ML_Syntax.MLE_Const
                                   (FStar_Extraction_ML_Syntax.MLC_Bool true)) in
                            (uu____6527, None, uu____6534) in
                          let uu____6536 =
                            let uu____6542 =
                              let uu____6547 =
                                FStar_All.pipe_left
                                  (FStar_Extraction_ML_Syntax.with_ty
                                     FStar_Extraction_ML_Syntax.ml_bool_ty)
                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                     (FStar_Extraction_ML_Syntax.MLC_Bool
                                        false)) in
                              (FStar_Extraction_ML_Syntax.MLP_Wild, None,
                                uu____6547) in
                            [uu____6542] in
                          uu____6522 :: uu____6536 in
                        (uu____6511, uu____6516) in
                      FStar_Extraction_ML_Syntax.MLE_Match uu____6503 in
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.ml_bool_ty) uu____6502 in
                  ((FStar_List.append wildcards [(mlid, targ)]), uu____6501) in
                FStar_Extraction_ML_Syntax.MLE_Fun uu____6495 in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty disc_ty) uu____6494 in
            let uu____6585 =
              let uu____6586 =
                let uu____6588 =
                  let uu____6589 =
                    FStar_Extraction_ML_UEnv.convIdent
                      discName.FStar_Ident.ident in
                  {
                    FStar_Extraction_ML_Syntax.mllb_name = uu____6589;
                    FStar_Extraction_ML_Syntax.mllb_tysc = None;
                    FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                    FStar_Extraction_ML_Syntax.mllb_def = discrBody;
                    FStar_Extraction_ML_Syntax.print_typ = false
                  } in
                [uu____6588] in
              (FStar_Extraction_ML_Syntax.NonRec, [], uu____6586) in
            FStar_Extraction_ML_Syntax.MLM_Let uu____6585