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
        else FStar_Extraction_ML_Syntax.E_IMPURE
let rec is_arity:
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t in
      let uu____261 =
        let uu____262 = FStar_Syntax_Subst.compress t1 in
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
          let t2 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Normalize.AllowUnboundUniverses;
              FStar_TypeChecker_Normalize.EraseUniverses;
              FStar_TypeChecker_Normalize.UnfoldUntil
                FStar_Syntax_Syntax.Delta_constant]
              env.FStar_Extraction_ML_UEnv.tcenv t1 in
          let uu____287 =
            let uu____288 = FStar_Syntax_Subst.compress t2 in
            uu____288.FStar_Syntax_Syntax.n in
          (match uu____287 with
           | FStar_Syntax_Syntax.Tm_fvar uu____291 -> false
           | uu____292 -> is_arity env t2)
      | FStar_Syntax_Syntax.Tm_app uu____293 ->
          let uu____303 = FStar_Syntax_Util.head_and_args t1 in
          (match uu____303 with | (head1,uu____314) -> is_arity env head1)
      | FStar_Syntax_Syntax.Tm_uinst (head1,uu____330) -> is_arity env head1
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
      let t1 = FStar_Syntax_Subst.compress t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed _|FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____452 =
            let uu____453 = FStar_Syntax_Print.tag_of_term t1 in
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
          if uu____460
          then true
          else
            (let uu____466 =
               FStar_TypeChecker_Env.lookup_lid
                 env.FStar_Extraction_ML_UEnv.tcenv
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
             match uu____466 with
             | ((uu____475,t2),uu____477) -> is_arity env t2)
      | FStar_Syntax_Syntax.Tm_uvar (_,t2)
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
           | (uu____600,uu____601,e)::uu____603 -> is_type_aux env e
           | uu____639 -> failwith "Empty branches")
      | FStar_Syntax_Syntax.Tm_meta (t2,uu____652) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_app (head1,uu____658) -> is_type_aux env head1
let is_type:
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let b = is_type_aux env t in
      FStar_Extraction_ML_UEnv.debug env
        (fun uu____681  ->
           if b
           then
             let uu____682 = FStar_Syntax_Print.term_to_string t in
             let uu____683 = FStar_Syntax_Print.tag_of_term t in
             FStar_Util.print2 "is_type %s (%s)\n" uu____682 uu____683
           else
             (let uu____685 = FStar_Syntax_Print.term_to_string t in
              let uu____686 = FStar_Syntax_Print.tag_of_term t in
              FStar_Util.print2 "not a type %s (%s)\n" uu____685 uu____686));
      b
let is_type_binder env x =
  is_arity env (Prims.fst x).FStar_Syntax_Syntax.sort
let is_constructor: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____706 =
      let uu____707 = FStar_Syntax_Subst.compress t in
      uu____707.FStar_Syntax_Syntax.n in
    match uu____706 with
    | FStar_Syntax_Syntax.Tm_fvar
      { FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _;
        FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor );_}
      |FStar_Syntax_Syntax.Tm_fvar
      { FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _;
        FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor
          _);_}
        -> true
    | uu____715 -> false
let rec is_fstar_value: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____719 =
      let uu____720 = FStar_Syntax_Subst.compress t in
      uu____720.FStar_Syntax_Syntax.n in
    match uu____719 with
    | FStar_Syntax_Syntax.Tm_constant _
      |FStar_Syntax_Syntax.Tm_bvar _
       |FStar_Syntax_Syntax.Tm_fvar _|FStar_Syntax_Syntax.Tm_abs _ -> true
    | FStar_Syntax_Syntax.Tm_app (head1,args) ->
        let uu____743 = is_constructor head1 in
        if uu____743
        then
          FStar_All.pipe_right args
            (FStar_List.for_all
               (fun uu____751  ->
                  match uu____751 with | (te,uu____755) -> is_fstar_value te))
        else false
    | FStar_Syntax_Syntax.Tm_meta (t1,_)|FStar_Syntax_Syntax.Tm_ascribed
      (t1,_,_) -> is_fstar_value t1
    | uu____781 -> false
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
    | FStar_Extraction_ML_Syntax.MLE_Record (uu____794,fields) ->
        FStar_Util.for_all
          (fun uu____806  ->
             match uu____806 with | (uu____809,e1) -> is_ml_value e1) fields
    | uu____811 -> false
let normalize_abs: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t0  ->
    let rec aux bs t copt =
      let t1 = FStar_Syntax_Subst.compress t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_abs (bs',body,copt1) ->
          aux (FStar_List.append bs bs') body copt1
      | uu____871 ->
          let e' = FStar_Syntax_Util.unascribe t1 in
          let uu____873 = FStar_Syntax_Util.is_fun e' in
          if uu____873
          then aux bs e' copt
          else FStar_Syntax_Util.abs bs e' copt in
    aux [] t0 None
let unit_binder: FStar_Syntax_Syntax.binder =
  let uu____882 =
    FStar_Syntax_Syntax.new_bv None FStar_TypeChecker_Common.t_unit in
  FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____882
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
      (let uu____926 = FStar_List.hd l in
       match uu____926 with
       | (p1,w1,e1) ->
           let uu____945 =
             let uu____950 = FStar_List.tl l in FStar_List.hd uu____950 in
           (match uu____945 with
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
                 | uu____989 -> def)))
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
            let uu____1032 = erasable g f ty in
            if uu____1032
            then
              let uu____1033 =
                type_leq g ty FStar_Extraction_ML_Syntax.ml_unit_ty in
              (if uu____1033
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
          let uu____1049 = (type_leq_c g (Some e) ty1) expect in
          match uu____1049 with
          | (true ,Some e') -> e'
          | uu____1055 ->
              (FStar_Extraction_ML_UEnv.debug g
                 (fun uu____1060  ->
                    let uu____1061 =
                      FStar_Extraction_ML_Code.string_of_mlexpr
                        g.FStar_Extraction_ML_UEnv.currentModule e in
                    let uu____1062 =
                      FStar_Extraction_ML_Code.string_of_mlty
                        g.FStar_Extraction_ML_UEnv.currentModule ty1 in
                    let uu____1063 =
                      FStar_Extraction_ML_Code.string_of_mlty
                        g.FStar_Extraction_ML_UEnv.currentModule expect in
                    FStar_Util.print3
                      "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n"
                      uu____1061 uu____1062 uu____1063);
               FStar_All.pipe_left
                 (FStar_Extraction_ML_Syntax.with_ty expect)
                 (FStar_Extraction_ML_Syntax.MLE_Coerce (e, ty1, expect)))
let bv_as_mlty:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlty
  =
  fun g  ->
    fun bv  ->
      let uu____1070 = FStar_Extraction_ML_UEnv.lookup_bv g bv in
      match uu____1070 with
      | FStar_Util.Inl (uu____1071,t) -> t
      | uu____1079 -> FStar_Extraction_ML_Syntax.MLTY_Top
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
      let uu____1113 =
        (fun t1  ->
           match t1 with
           | FStar_Extraction_ML_Syntax.MLTY_Top  -> true
           | FStar_Extraction_ML_Syntax.MLTY_Named uu____1115 ->
               let uu____1119 = FStar_Extraction_ML_Util.udelta_unfold g t1 in
               (match uu____1119 with
                | None  -> false
                | Some t2 ->
                    (let rec is_top_ty t3 =
                       match t3 with
                       | FStar_Extraction_ML_Syntax.MLTY_Top  -> true
                       | FStar_Extraction_ML_Syntax.MLTY_Named uu____1126 ->
                           let uu____1130 =
                             FStar_Extraction_ML_Util.udelta_unfold g t3 in
                           (match uu____1130 with
                            | None  -> false
                            | Some t4 -> is_top_ty t4)
                       | uu____1133 -> false in
                     is_top_ty) t2)
           | uu____1134 -> false) mlt in
      if uu____1113
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
          let uu____1142 =
            let uu____1143 = FStar_Syntax_Print.term_to_string t1 in
            FStar_Util.format1 "Impossible: Unexpected term %s" uu____1143 in
          failwith uu____1142
      | FStar_Syntax_Syntax.Tm_constant uu____1144 ->
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
          let uu____1208 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____1208 with
           | (bs1,c1) ->
               let uu____1213 = binders_as_ml_binders env bs1 in
               (match uu____1213 with
                | (mlbs,env1) ->
                    let t_ret =
                      let eff =
                        FStar_TypeChecker_Env.norm_eff_name
                          env1.FStar_Extraction_ML_UEnv.tcenv
                          (FStar_Syntax_Util.comp_effect_name c1) in
                      let ed =
                        FStar_TypeChecker_Env.get_effect_decl
                          env1.FStar_Extraction_ML_UEnv.tcenv eff in
                      let uu____1230 =
                        FStar_All.pipe_right
                          ed.FStar_Syntax_Syntax.qualifiers
                          (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
                      if uu____1230
                      then
                        let t2 =
                          FStar_TypeChecker_Env.reify_comp
                            env1.FStar_Extraction_ML_UEnv.tcenv c1
                            FStar_Syntax_Syntax.U_unknown in
                        let res = term_as_mlty' env1 t2 in res
                      else
                        term_as_mlty' env1 (FStar_Syntax_Util.comp_result c1) in
                    let erase1 =
                      effect_as_etag env1
                        (FStar_Syntax_Util.comp_effect_name c1) in
                    let uu____1236 =
                      FStar_List.fold_right
                        (fun uu____1243  ->
                           fun uu____1244  ->
                             match (uu____1243, uu____1244) with
                             | ((uu____1255,t2),(tag,t')) ->
                                 (FStar_Extraction_ML_Syntax.E_PURE,
                                   (FStar_Extraction_ML_Syntax.MLTY_Fun
                                      (t2, tag, t')))) mlbs (erase1, t_ret) in
                    (match uu____1236 with | (uu____1263,t2) -> t2)))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let res =
            let uu____1282 =
              let uu____1283 = FStar_Syntax_Util.un_uinst head1 in
              uu____1283.FStar_Syntax_Syntax.n in
            match uu____1282 with
            | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
            | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv args
            | FStar_Syntax_Syntax.Tm_app (head2,args') ->
                let uu____1304 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app
                       (head2, (FStar_List.append args' args))) None
                    t1.FStar_Syntax_Syntax.pos in
                term_as_mlty' env uu____1304
            | uu____1320 -> FStar_Extraction_ML_UEnv.unknownType in
          res
      | FStar_Syntax_Syntax.Tm_abs (bs,ty,uu____1323) ->
          let uu____1346 = FStar_Syntax_Subst.open_term bs ty in
          (match uu____1346 with
           | (bs1,ty1) ->
               let uu____1351 = binders_as_ml_binders env bs1 in
               (match uu____1351 with | (bts,env1) -> term_as_mlty' env1 ty1))
      | FStar_Syntax_Syntax.Tm_type _
        |FStar_Syntax_Syntax.Tm_let _|FStar_Syntax_Syntax.Tm_match _ ->
          FStar_Extraction_ML_UEnv.unknownType
and arg_as_mlty:
  FStar_Extraction_ML_UEnv.env ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.aqual) ->
      FStar_Extraction_ML_Syntax.mlty
  =
  fun g  ->
    fun uu____1369  ->
      match uu____1369 with
      | (a,uu____1373) ->
          let uu____1374 = is_type g a in
          if uu____1374
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
        let uu____1379 =
          FStar_Syntax_Util.arrow_formals
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.ty in
        match uu____1379 with
        | (formals,t) ->
            let mlargs = FStar_List.map (arg_as_mlty g) args in
            let mlargs1 =
              let n_args = FStar_List.length args in
              if (FStar_List.length formals) > n_args
              then
                let uu____1423 = FStar_Util.first_N n_args formals in
                match uu____1423 with
                | (uu____1437,rest) ->
                    let uu____1451 =
                      FStar_List.map
                        (fun uu____1455  ->
                           FStar_Extraction_ML_UEnv.erasedContent) rest in
                    FStar_List.append mlargs uu____1451
              else mlargs in
            let nm =
              let uu____1460 =
                FStar_Extraction_ML_UEnv.maybe_mangle_type_projector g fv in
              match uu____1460 with
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
      let uu____1475 =
        FStar_All.pipe_right bs
          (FStar_List.fold_left
             (fun uu____1499  ->
                fun b  ->
                  match uu____1499 with
                  | (ml_bs,env) ->
                      let uu____1529 = is_type_binder g b in
                      if uu____1529
                      then
                        let b1 = Prims.fst b in
                        let env1 =
                          FStar_Extraction_ML_UEnv.extend_ty env b1
                            (Some FStar_Extraction_ML_Syntax.MLTY_Top) in
                        let ml_b =
                          let uu____1544 =
                            FStar_Extraction_ML_UEnv.bv_as_ml_termvar b1 in
                          (uu____1544, FStar_Extraction_ML_Syntax.ml_unit_ty) in
                        ((ml_b :: ml_bs), env1)
                      else
                        (let b1 = Prims.fst b in
                         let t = term_as_mlty env b1.FStar_Syntax_Syntax.sort in
                         let uu____1561 =
                           FStar_Extraction_ML_UEnv.extend_bv env b1 
                             ([], t) false false false in
                         match uu____1561 with
                         | (env1,b2) ->
                             let ml_b =
                               let uu____1579 =
                                 FStar_Extraction_ML_UEnv.removeTick b2 in
                               (uu____1579, t) in
                             ((ml_b :: ml_bs), env1))) ([], g)) in
      match uu____1475 with | (ml_bs,env) -> ((FStar_List.rev ml_bs), env)
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
      | (FStar_Extraction_ML_Syntax.MLE_Seq es1,uu____1639) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (FStar_List.append es1 [e2])
      | (uu____1641,FStar_Extraction_ML_Syntax.MLE_Seq es2) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (e1 :: es2)
      | uu____1644 -> FStar_Extraction_ML_Syntax.MLE_Seq [e1; e2]
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
                    | uu____1666 when
                        (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
                          =
                          FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr
                        -> body.FStar_Extraction_ML_Syntax.expr
                    | uu____1667 ->
                        mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def
                          body)
             | uu____1668 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body))
        | uu____1670 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body)
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
           | uu____1684 ->
               (match q with
                | Some (FStar_Syntax_Syntax.Record_ctor (ty,fns)) ->
                    let path =
                      FStar_List.map FStar_Ident.text_of_id ty.FStar_Ident.ns in
                    let fs = record_fields fns pats in
                    FStar_Extraction_ML_Syntax.MLP_Record (path, fs)
                | uu____1700 -> p))
      | uu____1702 -> p
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
                       (fun uu____1741  ->
                          let uu____1742 =
                            FStar_Extraction_ML_Code.string_of_mlty
                              g.FStar_Extraction_ML_UEnv.currentModule t' in
                          let uu____1743 =
                            FStar_Extraction_ML_Code.string_of_mlty
                              g.FStar_Extraction_ML_UEnv.currentModule t in
                          FStar_Util.print2
                            "Expected pattern type %s; got pattern type %s\n"
                            uu____1742 uu____1743)
                   else ();
                   ok) in
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_disj uu____1752 ->
                failwith "Impossible: Nested disjunctive pattern"
            | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int
                (c,None )) ->
                let i = FStar_Const.Const_int (c, None) in
                let x = FStar_Extraction_ML_Syntax.gensym () in
                let when_clause =
                  let uu____1777 =
                    let uu____1778 =
                      let uu____1782 =
                        let uu____1784 =
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty
                               FStar_Extraction_ML_Syntax.ml_int_ty)
                            (FStar_Extraction_ML_Syntax.MLE_Var x) in
                        let uu____1785 =
                          let uu____1787 =
                            let uu____1788 =
                              let uu____1789 =
                                FStar_Extraction_ML_Util.mlconst_of_const'
                                  p.FStar_Syntax_Syntax.p i in
                              FStar_All.pipe_left
                                (fun _0_30  ->
                                   FStar_Extraction_ML_Syntax.MLE_Const _0_30)
                                uu____1789 in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.ml_int_ty)
                              uu____1788 in
                          [uu____1787] in
                        uu____1784 :: uu____1785 in
                      (FStar_Extraction_ML_Util.prims_op_equality,
                        uu____1782) in
                    FStar_Extraction_ML_Syntax.MLE_App uu____1778 in
                  FStar_All.pipe_left
                    (FStar_Extraction_ML_Syntax.with_ty
                       FStar_Extraction_ML_Syntax.ml_bool_ty) uu____1777 in
                let uu____1791 = ok FStar_Extraction_ML_Syntax.ml_int_ty in
                (g,
                  (Some
                     ((FStar_Extraction_ML_Syntax.MLP_Var x), [when_clause])),
                  uu____1791)
            | FStar_Syntax_Syntax.Pat_constant s ->
                let t =
                  FStar_TypeChecker_TcTerm.tc_constant FStar_Range.dummyRange
                    s in
                let mlty = term_as_mlty g t in
                let uu____1803 =
                  let uu____1808 =
                    let uu____1812 =
                      let uu____1813 =
                        FStar_Extraction_ML_Util.mlconst_of_const'
                          p.FStar_Syntax_Syntax.p s in
                      FStar_Extraction_ML_Syntax.MLP_Const uu____1813 in
                    (uu____1812, []) in
                  Some uu____1808 in
                let uu____1818 = ok mlty in (g, uu____1803, uu____1818)
            | FStar_Syntax_Syntax.Pat_wild x when disjunctive_pat ->
                (g, (Some (FStar_Extraction_ML_Syntax.MLP_Wild, [])), true)
            | FStar_Syntax_Syntax.Pat_var x|FStar_Syntax_Syntax.Pat_wild x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort in
                let uu____1834 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp in
                (match uu____1834 with
                 | (g1,x1) ->
                     let uu____1847 = ok mlty in
                     (g1,
                       (if imp
                        then None
                        else
                          Some ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                       uu____1847))
            | FStar_Syntax_Syntax.Pat_dot_term uu____1864 -> (g, None, true)
            | FStar_Syntax_Syntax.Pat_cons (f,pats) ->
                let uu____1888 =
                  let uu____1891 = FStar_Extraction_ML_UEnv.lookup_fv g f in
                  match uu____1891 with
                  | FStar_Util.Inr
                      (uu____1894,{
                                    FStar_Extraction_ML_Syntax.expr =
                                      FStar_Extraction_ML_Syntax.MLE_Name n1;
                                    FStar_Extraction_ML_Syntax.mlty =
                                      uu____1896;
                                    FStar_Extraction_ML_Syntax.loc =
                                      uu____1897;_},ttys,uu____1899)
                      -> (n1, ttys)
                  | uu____1906 -> failwith "Expected a constructor" in
                (match uu____1888 with
                 | (d,tys) ->
                     let nTyVars = FStar_List.length (Prims.fst tys) in
                     let uu____1920 = FStar_Util.first_N nTyVars pats in
                     (match uu____1920 with
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
                                                           p1 in
                                                       FStar_Util.print1
                                                         "Pattern %s is not extractable"
                                                         uu____2014);
                                                  Prims.raise Un_extractable)))) in
                              let f_ty =
                                FStar_Extraction_ML_Util.subst tys mlty_args in
                              let uu____2016 =
                                FStar_Extraction_ML_Util.uncurry_mlty_fun
                                  f_ty in
                              Some uu____2016
                            with | Un_extractable  -> None in
                          let uu____2031 =
                            FStar_Util.fold_map
                              (fun g1  ->
                                 fun uu____2046  ->
                                   match uu____2046 with
                                   | (p1,imp1) ->
                                       let uu____2057 =
                                         extract_one_pat disjunctive_pat true
                                           g1 p1 None in
                                       (match uu____2057 with
                                        | (g2,p2,uu____2073) -> (g2, p2))) g
                              tysVarPats in
                          (match uu____2031 with
                           | (g1,tyMLPats) ->
                               let uu____2105 =
                                 FStar_Util.fold_map
                                   (fun uu____2131  ->
                                      fun uu____2132  ->
                                        match (uu____2131, uu____2132) with
                                        | ((g2,f_ty_opt1),(p1,imp1)) ->
                                            let uu____2181 =
                                              match f_ty_opt1 with
                                              | Some (hd1::rest,res) ->
                                                  ((Some (rest, res)),
                                                    (Some hd1))
                                              | uu____2213 -> (None, None) in
                                            (match uu____2181 with
                                             | (f_ty_opt2,expected_ty) ->
                                                 let uu____2250 =
                                                   extract_one_pat
                                                     disjunctive_pat false g2
                                                     p1 expected_ty in
                                                 (match uu____2250 with
                                                  | (g3,p2,uu____2272) ->
                                                      ((g3, f_ty_opt2), p2))))
                                   (g1, f_ty_opt) restPats in
                               (match uu____2105 with
                                | ((g2,f_ty_opt1),restMLPats) ->
                                    let uu____2333 =
                                      let uu____2339 =
                                        FStar_All.pipe_right
                                          (FStar_List.append tyMLPats
                                             restMLPats)
                                          (FStar_List.collect
                                             (fun uu___136_2364  ->
                                                match uu___136_2364 with
                                                | Some x -> [x]
                                                | uu____2386 -> [])) in
                                      FStar_All.pipe_right uu____2339
                                        FStar_List.split in
                                    (match uu____2333 with
                                     | (mlPats,when_clauses) ->
                                         let pat_ty_compat =
                                           match f_ty_opt1 with
                                           | Some ([],t) -> ok t
                                           | uu____2425 -> false in
                                         let uu____2430 =
                                           let uu____2435 =
                                             let uu____2439 =
                                               resugar_pat
                                                 f.FStar_Syntax_Syntax.fv_qual
                                                 (FStar_Extraction_ML_Syntax.MLP_CTor
                                                    (d, mlPats)) in
                                             let uu____2441 =
                                               FStar_All.pipe_right
                                                 when_clauses
                                                 FStar_List.flatten in
                                             (uu____2439, uu____2441) in
                                           Some uu____2435 in
                                         (g2, uu____2430, pat_ty_compat))))))
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
          let uu____2502 = extract_one_pat disj false g1 p1 expected_t1 in
          match uu____2502 with
          | (g2,Some (x,v1),b) -> (g2, (x, v1), b)
          | uu____2533 -> failwith "Impossible: Unable to translate pattern" in
        let mk_when_clause whens =
          match whens with
          | [] -> None
          | hd1::tl1 ->
              let uu____2558 =
                FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd1 tl1 in
              Some uu____2558 in
        match p.FStar_Syntax_Syntax.v with
        | FStar_Syntax_Syntax.Pat_disj [] ->
            failwith "Impossible: Empty disjunctive pattern"
        | FStar_Syntax_Syntax.Pat_disj (p1::pats) ->
            let uu____2584 = extract_one_pat1 true g p1 (Some expected_t) in
            (match uu____2584 with
             | (g',p2,b) ->
                 let uu____2607 =
                   FStar_Util.fold_map
                     (fun b1  ->
                        fun p3  ->
                          let uu____2619 =
                            extract_one_pat1 true g p3 (Some expected_t) in
                          match uu____2619 with
                          | (uu____2631,p4,b') -> ((b1 && b'), p4)) b pats in
                 (match uu____2607 with
                  | (b1,ps) ->
                      let ps1 = p2 :: ps in
                      let g1 = g' in
                      let uu____2669 =
                        FStar_All.pipe_right ps1
                          (FStar_List.partition
                             (fun uu___137_2697  ->
                                match uu___137_2697 with
                                | (uu____2701,uu____2702::uu____2703) -> true
                                | uu____2706 -> false)) in
                      (match uu____2669 with
                       | (ps_when,rest) ->
                           let ps2 =
                             FStar_All.pipe_right ps_when
                               (FStar_List.map
                                  (fun uu____2754  ->
                                     match uu____2754 with
                                     | (x,whens) ->
                                         let uu____2765 =
                                           mk_when_clause whens in
                                         (x, uu____2765))) in
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
                                         uu____2805 in
                                     (uu____2804, None) in
                                   uu____2800 :: ps2 in
                                 (g1, uu____2795, b1) in
                           res)))
        | uu____2819 ->
            let uu____2820 = extract_one_pat1 false g p (Some expected_t) in
            (match uu____2820 with
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
            | FStar_Extraction_ML_Syntax.MLTY_Fun (t0,uu____2902,t1) ->
                let x = FStar_Extraction_ML_Syntax.gensym () in
                let uu____2905 =
                  let uu____2911 =
                    let uu____2916 =
                      FStar_All.pipe_left
                        (FStar_Extraction_ML_Syntax.with_ty t0)
                        (FStar_Extraction_ML_Syntax.MLE_Var x) in
                    ((x, t0), uu____2916) in
                  uu____2911 :: more_args in
                eta_args uu____2905 t1
            | FStar_Extraction_ML_Syntax.MLTY_Named (uu____2923,uu____2924)
                -> ((FStar_List.rev more_args), t)
            | uu____2936 -> failwith "Impossible: Head type is not an arrow" in
          let as_record qual1 e =
            match ((e.FStar_Extraction_ML_Syntax.expr), qual1) with
            | (FStar_Extraction_ML_Syntax.MLE_CTor (uu____2954,args),Some
               (FStar_Syntax_Syntax.Record_ctor (tyname,fields))) ->
                let path =
                  FStar_List.map FStar_Ident.text_of_id tyname.FStar_Ident.ns in
                let fields1 = record_fields fields args in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     e.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_Record (path, fields1))
            | uu____2973 -> e in
          let resugar_and_maybe_eta qual1 e =
            let uu____2986 = eta_args [] residualType in
            match uu____2986 with
            | (eargs,tres) ->
                (match eargs with
                 | [] ->
                     let uu____3014 = as_record qual1 e in
                     FStar_Extraction_ML_Util.resugar_exp uu____3014
                 | uu____3015 ->
                     let uu____3021 = FStar_List.unzip eargs in
                     (match uu____3021 with
                      | (binders,eargs1) ->
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
                                          (head1,
                                            (FStar_List.append args eargs1))) in
                                   FStar_All.pipe_left (as_record qual1)
                                     uu____3046 in
                                 FStar_All.pipe_left
                                   FStar_Extraction_ML_Util.resugar_exp
                                   uu____3045 in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    e.FStar_Extraction_ML_Syntax.mlty)
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    (binders, body))
                           | uu____3051 ->
                               failwith "Impossible: Not a constructor"))) in
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
                  (FStar_List.append constrname.FStar_Ident.ns [f]) in
              let fn = FStar_Extraction_ML_Util.mlpath_of_lid f1 in
              let proj = FStar_Extraction_ML_Syntax.MLE_Proj (mle, fn) in
              let e =
                match args with
                | [] -> proj
                | uu____3075 ->
                    let uu____3077 =
                      let uu____3081 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj in
                      (uu____3081, args) in
                    FStar_Extraction_ML_Syntax.MLE_App uu____3077 in
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
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs)) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____3096
          | (FStar_Extraction_ML_Syntax.MLE_Name mlp,Some
             (FStar_Syntax_Syntax.Data_ctor ))
            |(FStar_Extraction_ML_Syntax.MLE_Name mlp,Some
              (FStar_Syntax_Syntax.Record_ctor _)) ->
              let uu____3102 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, [])) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____3102
          | uu____3104 -> mlAppExpr
let maybe_downgrade_eff:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.e_tag ->
      FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.e_tag
  =
  fun g  ->
    fun f  ->
      fun t  ->
        let uu____3117 =
          (f = FStar_Extraction_ML_Syntax.E_GHOST) &&
            (type_leq g t FStar_Extraction_ML_Syntax.ml_unit_ty) in
        if uu____3117 then FStar_Extraction_ML_Syntax.E_PURE else f
let rec term_as_mlexpr:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Extraction_ML_Syntax.mlexpr* FStar_Extraction_ML_Syntax.e_tag*
        FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun t  ->
      let uu____3158 = term_as_mlexpr' g t in
      match uu____3158 with
      | (e,tag,ty) ->
          let tag1 = maybe_downgrade_eff g tag ty in
          (FStar_Extraction_ML_UEnv.debug g
             (fun u  ->
                let uu____3171 =
                  let uu____3172 = FStar_Syntax_Print.tag_of_term t in
                  let uu____3173 = FStar_Syntax_Print.term_to_string t in
                  let uu____3174 =
                    FStar_Extraction_ML_Code.string_of_mlty
                      g.FStar_Extraction_ML_UEnv.currentModule ty in
                  FStar_Util.format4
                    "term_as_mlexpr (%s) :  %s has ML type %s and effect %s\n"
                    uu____3172 uu____3173 uu____3174
                    (FStar_Extraction_ML_Util.eff_to_string tag1) in
                FStar_Util.print_string uu____3171);
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
          let uu____3181 = check_term_as_mlexpr' g t f ty in
          match uu____3181 with
          | (e,t1) ->
              let uu____3188 = erase g e t1 f in
              (match uu____3188 with | (r,uu____3195,t2) -> (r, t2))
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
          let uu____3203 = term_as_mlexpr g e0 in
          match uu____3203 with
          | (e,tag,t) ->
              let tag1 = maybe_downgrade_eff g tag t in
              if FStar_Extraction_ML_Util.eff_leq tag1 f
              then let uu____3215 = maybe_coerce g e t ty in (uu____3215, ty)
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
           let uu____3226 =
             let uu____3227 =
               FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos in
             let uu____3228 = FStar_Syntax_Print.tag_of_term top in
             let uu____3229 = FStar_Syntax_Print.term_to_string top in
             FStar_Util.format3 "%s: term_as_mlexpr' (%s) :  %s \n"
               uu____3227 uu____3228 uu____3229 in
           FStar_Util.print_string uu____3226);
      (let t = FStar_Syntax_Subst.compress top in
       match t.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_unknown 
         |FStar_Syntax_Syntax.Tm_delayed _
          |FStar_Syntax_Syntax.Tm_uvar _|FStar_Syntax_Syntax.Tm_bvar _ ->
           let uu____3237 =
             let uu____3238 = FStar_Syntax_Print.tag_of_term t in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____3238 in
           failwith uu____3237
       | FStar_Syntax_Syntax.Tm_type _
         |FStar_Syntax_Syntax.Tm_refine _|FStar_Syntax_Syntax.Tm_arrow _ ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Mutable_alloc ))
           ->
           let uu____3250 = term_as_mlexpr' g t1 in
           (match uu____3250 with
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
           (t1,FStar_Syntax_Syntax.Meta_monadic (m,uu____3286)) ->
           let t2 = FStar_Syntax_Subst.compress t1 in
           (match t2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) when
                FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname ->
                let ed =
                  FStar_TypeChecker_Env.get_effect_decl
                    g.FStar_Extraction_ML_UEnv.tcenv m in
                let uu____3310 =
                  let uu____3311 =
                    FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
                  FStar_All.pipe_right uu____3311 Prims.op_Negation in
                if uu____3310
                then term_as_mlexpr' g t2
                else
                  (let ml_result_ty_1 =
                     term_as_mlty g lb.FStar_Syntax_Syntax.lbtyp in
                   let uu____3318 =
                     term_as_mlexpr g lb.FStar_Syntax_Syntax.lbdef in
                   match uu____3318 with
                   | (comp_1,uu____3326,uu____3327) ->
                       let uu____3328 =
                         let k =
                           let uu____3332 =
                             let uu____3333 =
                               let uu____3334 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               FStar_All.pipe_right uu____3334
                                 FStar_Syntax_Syntax.mk_binder in
                             [uu____3333] in
                           FStar_Syntax_Util.abs uu____3332 body None in
                         let uu____3340 = term_as_mlexpr g k in
                         match uu____3340 with
                         | (ml_k,uu____3347,t_k) ->
                             let m_2 =
                               match t_k with
                               | FStar_Extraction_ML_Syntax.MLTY_Fun
                                   (uu____3350,uu____3351,m_2) -> m_2
                               | uu____3353 -> failwith "Impossible" in
                             (ml_k, m_2) in
                       (match uu____3328 with
                        | (ml_k,ty) ->
                            let bind1 =
                              let uu____3360 =
                                let uu____3361 =
                                  let uu____3362 =
                                    FStar_Extraction_ML_UEnv.monad_op_name ed
                                      "bind" in
                                  FStar_All.pipe_right uu____3362 Prims.fst in
                                FStar_Extraction_ML_Syntax.MLE_Name
                                  uu____3361 in
                              FStar_All.pipe_left
                                (FStar_Extraction_ML_Syntax.with_ty
                                   FStar_Extraction_ML_Syntax.MLTY_Top)
                                uu____3360 in
                            let uu____3367 =
                              FStar_All.pipe_left
                                (FStar_Extraction_ML_Syntax.with_ty ty)
                                (FStar_Extraction_ML_Syntax.MLE_App
                                   (bind1, [comp_1; ml_k])) in
                            (uu____3367, FStar_Extraction_ML_Syntax.E_IMPURE,
                              ty)))
            | uu____3369 -> term_as_mlexpr' g t2)
       | FStar_Syntax_Syntax.Tm_meta (t1,_)|FStar_Syntax_Syntax.Tm_uinst
         (t1,_) -> term_as_mlexpr' g t1
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____3382 =
             FStar_TypeChecker_TcTerm.type_of_tot_term
               g.FStar_Extraction_ML_UEnv.tcenv t in
           (match uu____3382 with
            | (uu____3389,ty,uu____3391) ->
                let ml_ty = term_as_mlty g ty in
                let uu____3393 =
                  let uu____3394 =
                    let uu____3395 =
                      FStar_Extraction_ML_Util.mlconst_of_const'
                        t.FStar_Syntax_Syntax.pos c in
                    FStar_All.pipe_left
                      (fun _0_31  ->
                         FStar_Extraction_ML_Syntax.MLE_Const _0_31)
                      uu____3395 in
                  FStar_Extraction_ML_Syntax.with_ty ml_ty uu____3394 in
                (uu____3393, FStar_Extraction_ML_Syntax.E_PURE, ml_ty))
       | FStar_Syntax_Syntax.Tm_name _|FStar_Syntax_Syntax.Tm_fvar _ ->
           let uu____3398 = is_type g t in
           if uu____3398
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____3403 = FStar_Extraction_ML_UEnv.lookup_term g t in
              match uu____3403 with
              | (FStar_Util.Inl uu____3410,uu____3411) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | (FStar_Util.Inr (uu____3430,x,mltys,uu____3433),qual) ->
                  (match mltys with
                   | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                       ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | ([],t1) ->
                       let uu____3458 =
                         maybe_eta_data_and_project_record g qual t1 x in
                       (uu____3458, FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | uu____3459 -> err_uninst g t mltys t))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,copt) ->
           let uu____3488 = FStar_Syntax_Subst.open_term bs body in
           (match uu____3488 with
            | (bs1,body1) ->
                let uu____3496 = binders_as_ml_binders g bs1 in
                (match uu____3496 with
                 | (ml_bs,env) ->
                     let uu____3513 = term_as_mlexpr env body1 in
                     (match uu____3513 with
                      | (ml_body,f,t1) ->
                          let uu____3523 =
                            FStar_List.fold_right
                              (fun uu____3530  ->
                                 fun uu____3531  ->
                                   match (uu____3530, uu____3531) with
                                   | ((uu____3542,targ),(f1,t2)) ->
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         (FStar_Extraction_ML_Syntax.MLTY_Fun
                                            (targ, f1, t2)))) ml_bs (f, t1) in
                          (match uu____3523 with
                           | (f1,tfun) ->
                               let uu____3555 =
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty tfun)
                                   (FStar_Extraction_ML_Syntax.MLE_Fun
                                      (ml_bs, ml_body)) in
                               (uu____3555, f1, tfun)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.tk = uu____3559;
              FStar_Syntax_Syntax.pos = uu____3560;
              FStar_Syntax_Syntax.vars = uu____3561;_},t1::[])
           ->
           let uu____3584 = term_as_mlexpr' g (Prims.fst t1) in
           (match uu____3584 with
            | (ml,e_tag,mlty) ->
                (ml, FStar_Extraction_ML_Syntax.E_PURE, mlty))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____3596);
              FStar_Syntax_Syntax.tk = uu____3597;
              FStar_Syntax_Syntax.pos = uu____3598;
              FStar_Syntax_Syntax.vars = uu____3599;_},t1::[])
           ->
           let uu____3622 = term_as_mlexpr' g (Prims.fst t1) in
           (match uu____3622 with
            | (ml,e_tag,mlty) ->
                (ml, FStar_Extraction_ML_Syntax.E_IMPURE, mlty))
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let is_total uu___139_3658 =
             match uu___139_3658 with
             | FStar_Util.Inl l -> FStar_Syntax_Util.is_total_lcomp l
             | FStar_Util.Inr (l,flags) ->
                 (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid)
                   ||
                   (FStar_All.pipe_right flags
                      (FStar_List.existsb
                         (fun uu___138_3676  ->
                            match uu___138_3676 with
                            | FStar_Syntax_Syntax.TOTAL  -> true
                            | uu____3677 -> false))) in
           let uu____3678 =
             let uu____3681 =
               let uu____3682 = FStar_Syntax_Subst.compress head1 in
               uu____3682.FStar_Syntax_Syntax.n in
             ((head1.FStar_Syntax_Syntax.n), uu____3681) in
           (match uu____3678 with
            | (FStar_Syntax_Syntax.Tm_uvar uu____3688,uu____3689) ->
                let t1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.Iota;
                    FStar_TypeChecker_Normalize.Zeta;
                    FStar_TypeChecker_Normalize.EraseUniverses;
                    FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                    g.FStar_Extraction_ML_UEnv.tcenv t in
                term_as_mlexpr' g t1
            | (uu____3699,FStar_Syntax_Syntax.Tm_abs (bs,uu____3701,Some lc))
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
            | uu____3730 ->
                let rec extract_app is_data uu____3758 uu____3759 restArgs =
                  match (uu____3758, uu____3759) with
                  | ((mlhead,mlargs_f),(f,t1)) ->
                      (match (restArgs, t1) with
                       | ([],uu____3807) ->
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
                                | uu____3821 -> false) in
                           let uu____3822 =
                             if evaluation_order_guaranteed
                             then
                               let uu____3835 =
                                 FStar_All.pipe_right
                                   (FStar_List.rev mlargs_f)
                                   (FStar_List.map Prims.fst) in
                               ([], uu____3835)
                             else
                               FStar_List.fold_left
                                 (fun uu____3860  ->
                                    fun uu____3861  ->
                                      match (uu____3860, uu____3861) with
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
                                             let uu____3916 =
                                               let uu____3918 =
                                                 FStar_All.pipe_left
                                                   (FStar_Extraction_ML_Syntax.with_ty
                                                      arg.FStar_Extraction_ML_Syntax.mlty)
                                                   (FStar_Extraction_ML_Syntax.MLE_Var
                                                      x) in
                                               uu____3918 :: out_args in
                                             (((x, arg) :: lbs), uu____3916)))
                                 ([], []) mlargs_f in
                           (match uu____3822 with
                            | (lbs,mlargs) ->
                                let app =
                                  let uu____3945 =
                                    FStar_All.pipe_left
                                      (FStar_Extraction_ML_Syntax.with_ty t1)
                                      (FStar_Extraction_ML_Syntax.MLE_App
                                         (mlhead, mlargs)) in
                                  FStar_All.pipe_left
                                    (maybe_eta_data_and_project_record g
                                       is_data t1) uu____3945 in
                                let l_app =
                                  FStar_List.fold_right
                                    (fun uu____3950  ->
                                       fun out  ->
                                         match uu____3950 with
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
                       | ((arg,uu____3963)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                          (formal_t,f',t2)) when is_type g arg ->
                           let uu____3981 =
                             type_leq g formal_t
                               FStar_Extraction_ML_Syntax.ml_unit_ty in
                           if uu____3981
                           then
                             let uu____3985 =
                               let uu____3988 =
                                 FStar_Extraction_ML_Util.join
                                   arg.FStar_Syntax_Syntax.pos f f' in
                               (uu____3988, t2) in
                             extract_app is_data
                               (mlhead,
                                 ((FStar_Extraction_ML_Syntax.ml_unit,
                                    FStar_Extraction_ML_Syntax.E_PURE) ::
                                 mlargs_f)) uu____3985 rest
                           else
                             (let uu____3995 =
                                let uu____3996 =
                                  FStar_Extraction_ML_Code.string_of_mlexpr
                                    g.FStar_Extraction_ML_UEnv.currentModule
                                    mlhead in
                                let uu____3997 =
                                  FStar_Syntax_Print.term_to_string arg in
                                let uu____3998 =
                                  FStar_Syntax_Print.tag_of_term arg in
                                let uu____3999 =
                                  FStar_Extraction_ML_Code.string_of_mlty
                                    g.FStar_Extraction_ML_UEnv.currentModule
                                    formal_t in
                                FStar_Util.format4
                                  "Impossible: ill-typed application:\n\thead=%s, arg=%s, tag=%s\n\texpected type unit, got %s"
                                  uu____3996 uu____3997 uu____3998 uu____3999 in
                              failwith uu____3995)
                       | ((e0,uu____4004)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                          (tExpected,f',t2)) ->
                           let r = e0.FStar_Syntax_Syntax.pos in
                           let uu____4023 = term_as_mlexpr g e0 in
                           (match uu____4023 with
                            | (e01,f0,tInferred) ->
                                let e02 =
                                  maybe_coerce g e01 tInferred tExpected in
                                let uu____4034 =
                                  let uu____4037 =
                                    FStar_Extraction_ML_Util.join_l r
                                      [f; f'; f0] in
                                  (uu____4037, t2) in
                                extract_app is_data
                                  (mlhead, ((e02, f0) :: mlargs_f))
                                  uu____4034 rest)
                       | uu____4043 ->
                           let uu____4050 =
                             FStar_Extraction_ML_Util.udelta_unfold g t1 in
                           (match uu____4050 with
                            | Some t2 ->
                                extract_app is_data (mlhead, mlargs_f)
                                  (f, t2) restArgs
                            | None  ->
                                err_ill_typed_application g top restArgs t1)) in
                let extract_app_maybe_projector is_data mlhead uu____4086
                  args1 =
                  match uu____4086 with
                  | (f,t1) ->
                      (match is_data with
                       | Some (FStar_Syntax_Syntax.Record_projector
                           uu____4105) ->
                           let rec remove_implicits args2 f1 t2 =
                             match (args2, t2) with
                             | ((a0,Some (FStar_Syntax_Syntax.Implicit
                                 uu____4155))::args3,FStar_Extraction_ML_Syntax.MLTY_Fun
                                (uu____4157,f',t3)) ->
                                 let uu____4182 =
                                   FStar_Extraction_ML_Util.join
                                     a0.FStar_Syntax_Syntax.pos f1 f' in
                                 remove_implicits args3 uu____4182 t3
                             | uu____4183 -> (args2, f1, t2) in
                           let uu____4198 = remove_implicits args1 f t1 in
                           (match uu____4198 with
                            | (args2,f1,t2) ->
                                extract_app is_data (mlhead, []) (f1, t2)
                                  args2)
                       | uu____4231 ->
                           extract_app is_data (mlhead, []) (f, t1) args1) in
                let uu____4238 = is_type g t in
                if uu____4238
                then
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
                else
                  (let head2 = FStar_Syntax_Util.un_uinst head1 in
                   match head2.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_name _
                     |FStar_Syntax_Syntax.Tm_fvar _ ->
                       let uu____4249 =
                         let uu____4256 =
                           FStar_Extraction_ML_UEnv.lookup_term g head2 in
                         match uu____4256 with
                         | (FStar_Util.Inr (uu____4266,x1,x2,x3),q) ->
                             ((x1, x2, x3), q)
                         | uu____4291 -> failwith "FIXME Ty" in
                       (match uu____4249 with
                        | ((head_ml,(vars,t1),inst_ok),qual) ->
                            let has_typ_apps =
                              match args with
                              | (a,uu____4320)::uu____4321 -> is_type g a
                              | uu____4335 -> false in
                            let uu____4341 =
                              match vars with
                              | uu____4358::uu____4359 when
                                  (Prims.op_Negation has_typ_apps) && inst_ok
                                  -> (head_ml, t1, args)
                              | uu____4366 ->
                                  let n1 = FStar_List.length vars in
                                  if n1 <= (FStar_List.length args)
                                  then
                                    let uu____4386 =
                                      FStar_Util.first_N n1 args in
                                    (match uu____4386 with
                                     | (prefix1,rest) ->
                                         let prefixAsMLTypes =
                                           FStar_List.map
                                             (fun uu____4439  ->
                                                match uu____4439 with
                                                | (x,uu____4443) ->
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
                                               let uu___143_4448 = head_ml in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (uu___143_4448.FStar_Extraction_ML_Syntax.expr);
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   = t2;
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___143_4448.FStar_Extraction_ML_Syntax.loc)
                                               }
                                           | FStar_Extraction_ML_Syntax.MLE_App
                                               (head3,{
                                                        FStar_Extraction_ML_Syntax.expr
                                                          =
                                                          FStar_Extraction_ML_Syntax.MLE_Const
                                                          (FStar_Extraction_ML_Syntax.MLC_Unit
                                                          );
                                                        FStar_Extraction_ML_Syntax.mlty
                                                          = uu____4450;
                                                        FStar_Extraction_ML_Syntax.loc
                                                          = uu____4451;_}::[])
                                               ->
                                               FStar_All.pipe_right
                                                 (FStar_Extraction_ML_Syntax.MLE_App
                                                    ((let uu___144_4454 =
                                                        head3 in
                                                      {
                                                        FStar_Extraction_ML_Syntax.expr
                                                          =
                                                          (uu___144_4454.FStar_Extraction_ML_Syntax.expr);
                                                        FStar_Extraction_ML_Syntax.mlty
                                                          =
                                                          (FStar_Extraction_ML_Syntax.MLTY_Fun
                                                             (FStar_Extraction_ML_Syntax.ml_unit_ty,
                                                               FStar_Extraction_ML_Syntax.E_PURE,
                                                               t2));
                                                        FStar_Extraction_ML_Syntax.loc
                                                          =
                                                          (uu___144_4454.FStar_Extraction_ML_Syntax.loc)
                                                      }),
                                                      [FStar_Extraction_ML_Syntax.ml_unit]))
                                                 (FStar_Extraction_ML_Syntax.with_ty
                                                    t2)
                                           | uu____4455 ->
                                               failwith
                                                 "Impossible: Unexpected head term" in
                                         (head3, t2, rest))
                                  else err_uninst g head2 (vars, t1) top in
                            (match uu____4341 with
                             | (head_ml1,head_t,args1) ->
                                 (match args1 with
                                  | [] ->
                                      let uu____4493 =
                                        maybe_eta_data_and_project_record g
                                          qual head_t head_ml1 in
                                      (uu____4493,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        head_t)
                                  | uu____4494 ->
                                      extract_app_maybe_projector qual
                                        head_ml1
                                        (FStar_Extraction_ML_Syntax.E_PURE,
                                          head_t) args1)))
                   | uu____4500 ->
                       let uu____4501 = term_as_mlexpr g head2 in
                       (match uu____4501 with
                        | (head3,f,t1) ->
                            extract_app_maybe_projector None head3 (f, t1)
                              args)))
       | FStar_Syntax_Syntax.Tm_ascribed (e0,(tc,uu____4513),f) ->
           let t1 =
             match tc with
             | FStar_Util.Inl t1 -> term_as_mlty g t1
             | FStar_Util.Inr c ->
                 term_as_mlty g (FStar_Syntax_Util.comp_result c) in
           let f1 =
             match f with
             | None  -> failwith "Ascription node with an empty effect label"
             | Some l -> effect_as_etag g l in
           let uu____4567 = check_term_as_mlexpr g e0 f1 t1 in
           (match uu____4567 with | (e,t2) -> (e, f1, t2))
       | FStar_Syntax_Syntax.Tm_let ((is_rec,lbs),e') ->
           let top_level = FStar_Syntax_Syntax.is_top_level lbs in
           let uu____4588 =
             if is_rec
             then FStar_Syntax_Subst.open_let_rec lbs e'
             else
               (let uu____4596 = FStar_Syntax_Syntax.is_top_level lbs in
                if uu____4596
                then (lbs, e')
                else
                  (let lb = FStar_List.hd lbs in
                   let x =
                     let uu____4606 =
                       FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                     FStar_Syntax_Syntax.freshen_bv uu____4606 in
                   let lb1 =
                     let uu___145_4608 = lb in
                     {
                       FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                       FStar_Syntax_Syntax.lbunivs =
                         (uu___145_4608.FStar_Syntax_Syntax.lbunivs);
                       FStar_Syntax_Syntax.lbtyp =
                         (uu___145_4608.FStar_Syntax_Syntax.lbtyp);
                       FStar_Syntax_Syntax.lbeff =
                         (uu___145_4608.FStar_Syntax_Syntax.lbeff);
                       FStar_Syntax_Syntax.lbdef =
                         (uu___145_4608.FStar_Syntax_Syntax.lbdef)
                     } in
                   let e'1 =
                     FStar_Syntax_Subst.subst
                       [FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x)] e' in
                   ([lb1], e'1))) in
           (match uu____4588 with
            | (lbs1,e'1) ->
                let lbs2 =
                  if top_level
                  then
                    FStar_All.pipe_right lbs1
                      (FStar_List.map
                         (fun lb  ->
                            let tcenv =
                              let uu____4625 =
                                FStar_Ident.lid_of_path
                                  (FStar_List.append
                                     (Prims.fst
                                        g.FStar_Extraction_ML_UEnv.currentModule)
                                     [Prims.snd
                                        g.FStar_Extraction_ML_UEnv.currentModule])
                                  FStar_Range.dummyRange in
                              FStar_TypeChecker_Env.set_current_module
                                g.FStar_Extraction_ML_UEnv.tcenv uu____4625 in
                            FStar_Extraction_ML_UEnv.debug g
                              (fun uu____4629  ->
                                 FStar_Options.set_option "debug_level"
                                   (FStar_Options.List
                                      [FStar_Options.String "Norm";
                                      FStar_Options.String "Extraction"]));
                            (let lbdef =
                               let uu____4633 = FStar_Options.ml_ish () in
                               if uu____4633
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
                             let uu___146_4637 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___146_4637.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___146_4637.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___146_4637.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___146_4637.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef
                             })))
                  else lbs1 in
                let maybe_generalize uu____4651 =
                  match uu____4651 with
                  | { FStar_Syntax_Syntax.lbname = lbname_;
                      FStar_Syntax_Syntax.lbunivs = uu____4662;
                      FStar_Syntax_Syntax.lbtyp = t1;
                      FStar_Syntax_Syntax.lbeff = lbeff;
                      FStar_Syntax_Syntax.lbdef = e;_} ->
                      let f_e = effect_as_etag g lbeff in
                      let t2 = FStar_Syntax_Subst.compress t1 in
                      (match t2.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                           let uu____4705 = FStar_List.hd bs in
                           FStar_All.pipe_right uu____4705 (is_type_binder g)
                           ->
                           let uu____4712 = FStar_Syntax_Subst.open_comp bs c in
                           (match uu____4712 with
                            | (bs1,c1) ->
                                let uu____4726 =
                                  let uu____4731 =
                                    FStar_Util.prefix_until
                                      (fun x  ->
                                         let uu____4749 = is_type_binder g x in
                                         Prims.op_Negation uu____4749) bs1 in
                                  match uu____4731 with
                                  | None  ->
                                      (bs1,
                                        (FStar_Syntax_Util.comp_result c1))
                                  | Some (bs2,b,rest) ->
                                      let uu____4797 =
                                        FStar_Syntax_Util.arrow (b :: rest)
                                          c1 in
                                      (bs2, uu____4797) in
                                (match uu____4726 with
                                 | (tbinders,tbody) ->
                                     let n_tbinders =
                                       FStar_List.length tbinders in
                                     let e1 =
                                       let uu____4827 = normalize_abs e in
                                       FStar_All.pipe_right uu____4827
                                         FStar_Syntax_Util.unmeta in
                                     (match e1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Tm_abs
                                          (bs2,body,uu____4839) ->
                                          let uu____4862 =
                                            FStar_Syntax_Subst.open_term bs2
                                              body in
                                          (match uu____4862 with
                                           | (bs3,body1) ->
                                               if
                                                 n_tbinders <=
                                                   (FStar_List.length bs3)
                                               then
                                                 let uu____4892 =
                                                   FStar_Util.first_N
                                                     n_tbinders bs3 in
                                                 (match uu____4892 with
                                                  | (targs,rest_args) ->
                                                      let expected_source_ty
                                                        =
                                                        let s =
                                                          FStar_List.map2
                                                            (fun uu____4935 
                                                               ->
                                                               fun uu____4936
                                                                  ->
                                                                 match 
                                                                   (uu____4935,
                                                                    uu____4936)
                                                                 with
                                                                 | ((x,uu____4946),
                                                                    (y,uu____4948))
                                                                    ->
                                                                    let uu____4953
                                                                    =
                                                                    let uu____4958
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    y in
                                                                    (x,
                                                                    uu____4958) in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____4953)
                                                            tbinders targs in
                                                        FStar_Syntax_Subst.subst
                                                          s tbody in
                                                      let env =
                                                        FStar_List.fold_left
                                                          (fun env  ->
                                                             fun uu____4963 
                                                               ->
                                                               match uu____4963
                                                               with
                                                               | (a,uu____4967)
                                                                   ->
                                                                   FStar_Extraction_ML_UEnv.extend_ty
                                                                    env a
                                                                    None) g
                                                          targs in
                                                      let expected_t =
                                                        term_as_mlty env
                                                          expected_source_ty in
                                                      let polytype =
                                                        let uu____4975 =
                                                          FStar_All.pipe_right
                                                            targs
                                                            (FStar_List.map
                                                               (fun
                                                                  uu____4989 
                                                                  ->
                                                                  match uu____4989
                                                                  with
                                                                  | (x,uu____4995)
                                                                    ->
                                                                    FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                                    x)) in
                                                        (uu____4975,
                                                          expected_t) in
                                                      let add_unit =
                                                        match rest_args with
                                                        | [] ->
                                                            let uu____5002 =
                                                              is_fstar_value
                                                                body1 in
                                                            Prims.op_Negation
                                                              uu____5002
                                                        | uu____5003 -> false in
                                                      let rest_args1 =
                                                        if add_unit
                                                        then unit_binder ::
                                                          rest_args
                                                        else rest_args in
                                                      let body2 =
                                                        match rest_args1 with
                                                        | [] -> body1
                                                        | uu____5012 ->
                                                            FStar_Syntax_Util.abs
                                                              rest_args1
                                                              body1 None in
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
                                                 fun uu____5068  ->
                                                   match uu____5068 with
                                                   | (a,uu____5072) ->
                                                       FStar_Extraction_ML_UEnv.extend_ty
                                                         env a None) g
                                              tbinders in
                                          let expected_t =
                                            term_as_mlty env tbody in
                                          let polytype =
                                            let uu____5080 =
                                              FStar_All.pipe_right tbinders
                                                (FStar_List.map
                                                   (fun uu____5091  ->
                                                      match uu____5091 with
                                                      | (x,uu____5097) ->
                                                          FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                            x)) in
                                            (uu____5080, expected_t) in
                                          let args =
                                            FStar_All.pipe_right tbinders
                                              (FStar_List.map
                                                 (fun uu____5106  ->
                                                    match uu____5106 with
                                                    | (bv,uu____5110) ->
                                                        let uu____5111 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            bv in
                                                        FStar_All.pipe_right
                                                          uu____5111
                                                          FStar_Syntax_Syntax.as_arg)) in
                                          let e2 =
                                            (FStar_Syntax_Syntax.mk
                                               (FStar_Syntax_Syntax.Tm_app
                                                  (e1, args))) None
                                              e1.FStar_Syntax_Syntax.pos in
                                          (lbname_, f_e,
                                            (t2, (tbinders, polytype)),
                                            false, e2)
                                      | uu____5149 ->
                                          err_value_restriction e1)))
                       | uu____5159 ->
                           let expected_t = term_as_mlty g t2 in
                           (lbname_, f_e, (t2, ([], ([], expected_t))),
                             false, e)) in
                let check_lb env uu____5216 =
                  match uu____5216 with
                  | (nm,(lbname,f,(t1,(targs,polytype)),add_unit,e)) ->
                      let env1 =
                        FStar_List.fold_left
                          (fun env1  ->
                             fun uu____5287  ->
                               match uu____5287 with
                               | (a,uu____5291) ->
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
                      let uu____5294 =
                        check_term_as_mlexpr env1 e f expected_t in
                      (match uu____5294 with
                       | (e1,uu____5300) ->
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
                let uu____5335 =
                  FStar_List.fold_right
                    (fun lb  ->
                       fun uu____5374  ->
                         match uu____5374 with
                         | (env,lbs4) ->
                             let uu____5438 = lb in
                             (match uu____5438 with
                              | (lbname,uu____5463,(t1,(uu____5465,polytype)),add_unit,uu____5468)
                                  ->
                                  let uu____5475 =
                                    FStar_Extraction_ML_UEnv.extend_lb env
                                      lbname t1 polytype add_unit true in
                                  (match uu____5475 with
                                   | (env1,nm) -> (env1, ((nm, lb) :: lbs4)))))
                    lbs3 (g, []) in
                (match uu____5335 with
                 | (env_body,lbs4) ->
                     let env_def = if is_rec then env_body else g in
                     let lbs5 =
                       FStar_All.pipe_right lbs4
                         (FStar_List.map (check_lb env_def)) in
                     let e'_rng = e'1.FStar_Syntax_Syntax.pos in
                     let uu____5618 = term_as_mlexpr env_body e'1 in
                     (match uu____5618 with
                      | (e'2,f',t') ->
                          let f =
                            let uu____5629 =
                              let uu____5631 = FStar_List.map Prims.fst lbs5 in
                              f' :: uu____5631 in
                            FStar_Extraction_ML_Util.join_l e'_rng uu____5629 in
                          let is_rec1 =
                            if is_rec = true
                            then FStar_Extraction_ML_Syntax.Rec
                            else FStar_Extraction_ML_Syntax.NonRec in
                          let uu____5637 =
                            let uu____5638 =
                              let uu____5639 =
                                let uu____5640 =
                                  FStar_List.map Prims.snd lbs5 in
                                (is_rec1, [], uu____5640) in
                              mk_MLE_Let top_level uu____5639 e'2 in
                            let uu____5646 =
                              FStar_Extraction_ML_Util.mlloc_of_range
                                t.FStar_Syntax_Syntax.pos in
                            FStar_Extraction_ML_Syntax.with_ty_loc t'
                              uu____5638 uu____5646 in
                          (uu____5637, f, t'))))
       | FStar_Syntax_Syntax.Tm_match (scrutinee,pats) ->
           let uu____5675 = term_as_mlexpr g scrutinee in
           (match uu____5675 with
            | (e,f_e,t_e) ->
                let uu____5685 = check_pats_for_ite pats in
                (match uu____5685 with
                 | (b,then_e,else_e) ->
                     let no_lift x t1 = x in
                     if b
                     then
                       (match (then_e, else_e) with
                        | (Some then_e1,Some else_e1) ->
                            let uu____5720 = term_as_mlexpr g then_e1 in
                            (match uu____5720 with
                             | (then_mle,f_then,t_then) ->
                                 let uu____5730 = term_as_mlexpr g else_e1 in
                                 (match uu____5730 with
                                  | (else_mle,f_else,t_else) ->
                                      let uu____5740 =
                                        let uu____5747 =
                                          type_leq g t_then t_else in
                                        if uu____5747
                                        then (t_else, no_lift)
                                        else
                                          (let uu____5759 =
                                             type_leq g t_else t_then in
                                           if uu____5759
                                           then (t_then, no_lift)
                                           else
                                             (FStar_Extraction_ML_Syntax.MLTY_Top,
                                               FStar_Extraction_ML_Syntax.apply_obj_repr)) in
                                      (match uu____5740 with
                                       | (t_branch,maybe_lift) ->
                                           let uu____5788 =
                                             let uu____5789 =
                                               let uu____5790 =
                                                 let uu____5795 =
                                                   maybe_lift then_mle t_then in
                                                 let uu____5796 =
                                                   let uu____5798 =
                                                     maybe_lift else_mle
                                                       t_else in
                                                   Some uu____5798 in
                                                 (e, uu____5795, uu____5796) in
                                               FStar_Extraction_ML_Syntax.MLE_If
                                                 uu____5790 in
                                             FStar_All.pipe_left
                                               (FStar_Extraction_ML_Syntax.with_ty
                                                  t_branch) uu____5789 in
                                           let uu____5800 =
                                             FStar_Extraction_ML_Util.join
                                               then_e1.FStar_Syntax_Syntax.pos
                                               f_then f_else in
                                           (uu____5788, uu____5800, t_branch))))
                        | uu____5801 ->
                            failwith
                              "ITE pats matched but then and else expressions not found?")
                     else
                       (let uu____5810 =
                          FStar_All.pipe_right pats
                            (FStar_Util.fold_map
                               (fun compat  ->
                                  fun br  ->
                                    let uu____5860 =
                                      FStar_Syntax_Subst.open_branch br in
                                    match uu____5860 with
                                    | (pat,when_opt,branch1) ->
                                        let uu____5890 =
                                          extract_pat g pat t_e in
                                        (match uu____5890 with
                                         | (env,p,pat_t_compat) ->
                                             let uu____5921 =
                                               match when_opt with
                                               | None  ->
                                                   (None,
                                                     FStar_Extraction_ML_Syntax.E_PURE)
                                               | Some w ->
                                                   let uu____5936 =
                                                     term_as_mlexpr env w in
                                                   (match uu____5936 with
                                                    | (w1,f_w,t_w) ->
                                                        let w2 =
                                                          maybe_coerce env w1
                                                            t_w
                                                            FStar_Extraction_ML_Syntax.ml_bool_ty in
                                                        ((Some w2), f_w)) in
                                             (match uu____5921 with
                                              | (when_opt1,f_when) ->
                                                  let uu____5964 =
                                                    term_as_mlexpr env
                                                      branch1 in
                                                  (match uu____5964 with
                                                   | (mlbranch,f_branch,t_branch)
                                                       ->
                                                       let uu____5983 =
                                                         FStar_All.pipe_right
                                                           p
                                                           (FStar_List.map
                                                              (fun uu____6020
                                                                  ->
                                                                 match uu____6020
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
                                                         uu____5983))))) true) in
                        match uu____5810 with
                        | (pat_t_compat,mlbranches) ->
                            let mlbranches1 = FStar_List.flatten mlbranches in
                            let e1 =
                              if pat_t_compat
                              then e
                              else
                                (FStar_Extraction_ML_UEnv.debug g
                                   (fun uu____6106  ->
                                      let uu____6107 =
                                        FStar_Extraction_ML_Code.string_of_mlexpr
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          e in
                                      let uu____6108 =
                                        FStar_Extraction_ML_Code.string_of_mlty
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          t_e in
                                      FStar_Util.print2
                                        "Coercing scrutinee %s from type %s because pattern type is incompatible\n"
                                        uu____6107 uu____6108);
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty t_e)
                                   (FStar_Extraction_ML_Syntax.MLE_Coerce
                                      (e, t_e,
                                        FStar_Extraction_ML_Syntax.MLTY_Top))) in
                            (match mlbranches1 with
                             | [] ->
                                 let uu____6121 =
                                   let uu____6126 =
                                     let uu____6135 =
                                       FStar_Syntax_Syntax.lid_as_fv
                                         FStar_Syntax_Const.failwith_lid
                                         FStar_Syntax_Syntax.Delta_constant
                                         None in
                                     FStar_Extraction_ML_UEnv.lookup_fv g
                                       uu____6135 in
                                   FStar_All.pipe_left FStar_Util.right
                                     uu____6126 in
                                 (match uu____6121 with
                                  | (uu____6157,fw,uu____6159,uu____6160) ->
                                      let uu____6161 =
                                        let uu____6162 =
                                          let uu____6163 =
                                            let uu____6167 =
                                              let uu____6169 =
                                                FStar_All.pipe_left
                                                  (FStar_Extraction_ML_Syntax.with_ty
                                                     FStar_Extraction_ML_Syntax.ml_string_ty)
                                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                                     (FStar_Extraction_ML_Syntax.MLC_String
                                                        "unreachable")) in
                                              [uu____6169] in
                                            (fw, uu____6167) in
                                          FStar_Extraction_ML_Syntax.MLE_App
                                            uu____6163 in
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             FStar_Extraction_ML_Syntax.ml_unit_ty)
                                          uu____6162 in
                                      (uu____6161,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        FStar_Extraction_ML_Syntax.ml_unit_ty))
                             | (uu____6171,uu____6172,(uu____6173,f_first,t_first))::rest
                                 ->
                                 let uu____6205 =
                                   FStar_List.fold_left
                                     (fun uu____6221  ->
                                        fun uu____6222  ->
                                          match (uu____6221, uu____6222) with
                                          | ((topt,f),(uu____6252,uu____6253,
                                                       (uu____6254,f_branch,t_branch)))
                                              ->
                                              let f1 =
                                                FStar_Extraction_ML_Util.join
                                                  top.FStar_Syntax_Syntax.pos
                                                  f f_branch in
                                              let topt1 =
                                                match topt with
                                                | None  -> None
                                                | Some t1 ->
                                                    let uu____6285 =
                                                      type_leq g t1 t_branch in
                                                    if uu____6285
                                                    then Some t_branch
                                                    else
                                                      (let uu____6288 =
                                                         type_leq g t_branch
                                                           t1 in
                                                       if uu____6288
                                                       then Some t1
                                                       else None) in
                                              (topt1, f1))
                                     ((Some t_first), f_first) rest in
                                 (match uu____6205 with
                                  | (topt,f_match) ->
                                      let mlbranches2 =
                                        FStar_All.pipe_right mlbranches1
                                          (FStar_List.map
                                             (fun uu____6334  ->
                                                match uu____6334 with
                                                | (p,(wopt,uu____6350),
                                                   (b1,uu____6352,t1)) ->
                                                    let b2 =
                                                      match topt with
                                                      | None  ->
                                                          FStar_Extraction_ML_Syntax.apply_obj_repr
                                                            b1 t1
                                                      | Some uu____6363 -> b1 in
                                                    (p, wopt, b2))) in
                                      let t_match =
                                        match topt with
                                        | None  ->
                                            FStar_Extraction_ML_Syntax.MLTY_Top
                                        | Some t1 -> t1 in
                                      let uu____6367 =
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             t_match)
                                          (FStar_Extraction_ML_Syntax.MLE_Match
                                             (e1, mlbranches2)) in
                                      (uu____6367, f_match, t_match)))))))
let fresh: Prims.string -> (Prims.string* Prims.int) =
  let c = FStar_Util.mk_ref (Prims.parse_int "0") in
  fun x  ->
    FStar_Util.incr c; (let uu____6385 = FStar_ST.read c in (x, uu____6385))
let ind_discriminator_body:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlmodule1
  =
  fun env  ->
    fun discName  ->
      fun constrName  ->
        let uu____6397 =
          let uu____6400 =
            FStar_TypeChecker_Env.lookup_lid
              env.FStar_Extraction_ML_UEnv.tcenv discName in
          FStar_All.pipe_left Prims.fst uu____6400 in
        match uu____6397 with
        | (uu____6413,fstar_disc_type) ->
            let wildcards =
              let uu____6421 =
                let uu____6422 = FStar_Syntax_Subst.compress fstar_disc_type in
                uu____6422.FStar_Syntax_Syntax.n in
              match uu____6421 with
              | FStar_Syntax_Syntax.Tm_arrow (binders,uu____6431) ->
                  let uu____6442 =
                    FStar_All.pipe_right binders
                      (FStar_List.filter
                         (fun uu___140_6457  ->
                            match uu___140_6457 with
                            | (uu____6461,Some (FStar_Syntax_Syntax.Implicit
                               uu____6462)) -> true
                            | uu____6464 -> false)) in
                  FStar_All.pipe_right uu____6442
                    (FStar_List.map
                       (fun uu____6484  ->
                          let uu____6488 = fresh "_" in
                          (uu____6488, FStar_Extraction_ML_Syntax.MLTY_Top)))
              | uu____6493 -> failwith "Discriminator must be a function" in
            let mlid = fresh "_discr_" in
            let targ = FStar_Extraction_ML_Syntax.MLTY_Top in
            let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top in
            let discrBody =
              let uu____6505 =
                let uu____6506 =
                  let uu____6512 =
                    let uu____6513 =
                      let uu____6514 =
                        let uu____6522 =
                          let uu____6523 =
                            let uu____6524 =
                              let uu____6525 =
                                FStar_Extraction_ML_Syntax.idsym mlid in
                              ([], uu____6525) in
                            FStar_Extraction_ML_Syntax.MLE_Name uu____6524 in
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty targ)
                            uu____6523 in
                        let uu____6527 =
                          let uu____6533 =
                            let uu____6538 =
                              let uu____6539 =
                                let uu____6543 =
                                  FStar_Extraction_ML_Syntax.mlpath_of_lident
                                    constrName in
                                (uu____6543,
                                  [FStar_Extraction_ML_Syntax.MLP_Wild]) in
                              FStar_Extraction_ML_Syntax.MLP_CTor uu____6539 in
                            let uu____6545 =
                              FStar_All.pipe_left
                                (FStar_Extraction_ML_Syntax.with_ty
                                   FStar_Extraction_ML_Syntax.ml_bool_ty)
                                (FStar_Extraction_ML_Syntax.MLE_Const
                                   (FStar_Extraction_ML_Syntax.MLC_Bool true)) in
                            (uu____6538, None, uu____6545) in
                          let uu____6547 =
                            let uu____6553 =
                              let uu____6558 =
                                FStar_All.pipe_left
                                  (FStar_Extraction_ML_Syntax.with_ty
                                     FStar_Extraction_ML_Syntax.ml_bool_ty)
                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                     (FStar_Extraction_ML_Syntax.MLC_Bool
                                        false)) in
                              (FStar_Extraction_ML_Syntax.MLP_Wild, None,
                                uu____6558) in
                            [uu____6553] in
                          uu____6533 :: uu____6547 in
                        (uu____6522, uu____6527) in
                      FStar_Extraction_ML_Syntax.MLE_Match uu____6514 in
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.ml_bool_ty) uu____6513 in
                  ((FStar_List.append wildcards [(mlid, targ)]), uu____6512) in
                FStar_Extraction_ML_Syntax.MLE_Fun uu____6506 in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty disc_ty) uu____6505 in
            let uu____6596 =
              let uu____6597 =
                let uu____6599 =
                  let uu____6600 =
                    FStar_Extraction_ML_UEnv.convIdent
                      discName.FStar_Ident.ident in
                  {
                    FStar_Extraction_ML_Syntax.mllb_name = uu____6600;
                    FStar_Extraction_ML_Syntax.mllb_tysc = None;
                    FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                    FStar_Extraction_ML_Syntax.mllb_def = discrBody;
                    FStar_Extraction_ML_Syntax.print_typ = false
                  } in
                [uu____6599] in
              (FStar_Extraction_ML_Syntax.NonRec, [], uu____6597) in
            FStar_Extraction_ML_Syntax.MLM_Let uu____6596