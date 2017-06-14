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
    FStar_Extraction_ML_Syntax.mlexpr option ->
      FStar_Extraction_ML_Syntax.mlty ->
        FStar_Extraction_ML_Syntax.mlty ->
          (Prims.bool* FStar_Extraction_ML_Syntax.mlexpr option)
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
            FStar_All.pipe_right vars (FStar_List.map FStar_Pervasives.fst) in
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
      | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____283 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_ascribed uu____304 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_meta uu____322 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_uvar uu____327 -> false
      | FStar_Syntax_Syntax.Tm_constant uu____338 -> false
      | FStar_Syntax_Syntax.Tm_name uu____339 -> false
      | FStar_Syntax_Syntax.Tm_bvar uu____340 -> false
      | FStar_Syntax_Syntax.Tm_type uu____341 -> true
      | FStar_Syntax_Syntax.Tm_arrow (uu____342,c) ->
          is_arity env (FStar_Syntax_Util.comp_result c)
      | FStar_Syntax_Syntax.Tm_fvar uu____354 ->
          let t2 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Normalize.AllowUnboundUniverses;
              FStar_TypeChecker_Normalize.EraseUniverses;
              FStar_TypeChecker_Normalize.UnfoldUntil
                FStar_Syntax_Syntax.Delta_constant]
              env.FStar_Extraction_ML_UEnv.tcenv t1 in
          let uu____356 =
            let uu____357 = FStar_Syntax_Subst.compress t2 in
            uu____357.FStar_Syntax_Syntax.n in
          (match uu____356 with
           | FStar_Syntax_Syntax.Tm_fvar uu____360 -> false
           | uu____361 -> is_arity env t2)
      | FStar_Syntax_Syntax.Tm_app uu____362 ->
          let uu____372 = FStar_Syntax_Util.head_and_args t1 in
          (match uu____372 with | (head1,uu____383) -> is_arity env head1)
      | FStar_Syntax_Syntax.Tm_uinst (head1,uu____399) -> is_arity env head1
      | FStar_Syntax_Syntax.Tm_refine (x,uu____405) ->
          is_arity env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_abs (uu____410,body,uu____412) ->
          is_arity env body
      | FStar_Syntax_Syntax.Tm_let (uu____435,body) -> is_arity env body
      | FStar_Syntax_Syntax.Tm_match (uu____447,branches) ->
          (match branches with
           | (uu____473,uu____474,e)::uu____476 -> is_arity env e
           | uu____508 -> false)
let rec is_type_aux:
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Subst.compress t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____526 ->
          let uu____547 =
            let uu____548 = FStar_Syntax_Print.tag_of_term t1 in
            FStar_Util.format1 "Impossible: %s" uu____548 in
          failwith uu____547
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____549 =
            let uu____550 = FStar_Syntax_Print.tag_of_term t1 in
            FStar_Util.format1 "Impossible: %s" uu____550 in
          failwith uu____549
      | FStar_Syntax_Syntax.Tm_constant uu____551 -> false
      | FStar_Syntax_Syntax.Tm_type uu____552 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____553 -> true
      | FStar_Syntax_Syntax.Tm_arrow uu____558 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.failwith_lid ->
          false
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____568 =
            FStar_TypeChecker_Env.is_type_constructor
              env.FStar_Extraction_ML_UEnv.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          if uu____568
          then true
          else
            (let uu____570 =
               FStar_TypeChecker_Env.lookup_lid
                 env.FStar_Extraction_ML_UEnv.tcenv
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
             match uu____570 with
             | ((uu____575,t2),uu____577) -> is_arity env t2)
      | FStar_Syntax_Syntax.Tm_uvar (uu____580,t2) -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_bvar
          { FStar_Syntax_Syntax.ppname = uu____598;
            FStar_Syntax_Syntax.index = uu____599;
            FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_name
          { FStar_Syntax_Syntax.ppname = uu____603;
            FStar_Syntax_Syntax.index = uu____604;
            FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____609,uu____610) ->
          is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____640) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_abs (uu____645,body,uu____647) ->
          is_type_aux env body
      | FStar_Syntax_Syntax.Tm_let (uu____670,body) -> is_type_aux env body
      | FStar_Syntax_Syntax.Tm_match (uu____682,branches) ->
          (match branches with
           | (uu____708,uu____709,e)::uu____711 -> is_type_aux env e
           | uu____743 -> false)
      | FStar_Syntax_Syntax.Tm_meta (t2,uu____755) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_app (head1,uu____761) -> is_type_aux env head1
let is_type:
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let b = is_type_aux env t in
      FStar_Extraction_ML_UEnv.debug env
        (fun uu____784  ->
           if b
           then
             let uu____785 = FStar_Syntax_Print.term_to_string t in
             let uu____786 = FStar_Syntax_Print.tag_of_term t in
             FStar_Util.print2 "is_type %s (%s)\n" uu____785 uu____786
           else
             (let uu____788 = FStar_Syntax_Print.term_to_string t in
              let uu____789 = FStar_Syntax_Print.tag_of_term t in
              FStar_Util.print2 "not a type %s (%s)\n" uu____788 uu____789));
      b
let is_type_binder env x = is_arity env (fst x).FStar_Syntax_Syntax.sort
let is_constructor: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____809 =
      let uu____810 = FStar_Syntax_Subst.compress t in
      uu____810.FStar_Syntax_Syntax.n in
    match uu____809 with
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____813;
          FStar_Syntax_Syntax.fv_delta = uu____814;
          FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor );_}
        -> true
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____815;
          FStar_Syntax_Syntax.fv_delta = uu____816;
          FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor
            uu____817);_}
        -> true
    | uu____821 -> false
let rec is_fstar_value: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____825 =
      let uu____826 = FStar_Syntax_Subst.compress t in
      uu____826.FStar_Syntax_Syntax.n in
    match uu____825 with
    | FStar_Syntax_Syntax.Tm_constant uu____829 -> true
    | FStar_Syntax_Syntax.Tm_bvar uu____830 -> true
    | FStar_Syntax_Syntax.Tm_fvar uu____831 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____832 -> true
    | FStar_Syntax_Syntax.Tm_app (head1,args) ->
        let uu____863 = is_constructor head1 in
        if uu____863
        then
          FStar_All.pipe_right args
            (FStar_List.for_all
               (fun uu____871  ->
                  match uu____871 with | (te,uu____875) -> is_fstar_value te))
        else false
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____878) -> is_fstar_value t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____884,uu____885) ->
        is_fstar_value t1
    | uu____914 -> false
let rec is_ml_value: FStar_Extraction_ML_Syntax.mlexpr -> Prims.bool =
  fun e  ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_Const uu____918 -> true
    | FStar_Extraction_ML_Syntax.MLE_Var uu____919 -> true
    | FStar_Extraction_ML_Syntax.MLE_Name uu____920 -> true
    | FStar_Extraction_ML_Syntax.MLE_Fun uu____921 -> true
    | FStar_Extraction_ML_Syntax.MLE_CTor (uu____927,exps) ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Tuple exps ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Record (uu____933,fields) ->
        FStar_Util.for_all
          (fun uu____945  ->
             match uu____945 with | (uu____948,e1) -> is_ml_value e1) fields
    | uu____950 -> false
let normalize_abs: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t0  ->
    let rec aux bs t copt =
      let t1 = FStar_Syntax_Subst.compress t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_abs (bs',body,copt1) ->
          aux (FStar_List.append bs bs') body copt1
      | uu____1010 ->
          let e' = FStar_Syntax_Util.unascribe t1 in
          let uu____1012 = FStar_Syntax_Util.is_fun e' in
          if uu____1012
          then aux bs e' copt
          else FStar_Syntax_Util.abs bs e' copt in
    aux [] t0 None
let unit_binder: FStar_Syntax_Syntax.binder =
  let uu____1021 =
    FStar_Syntax_Syntax.new_bv None FStar_TypeChecker_Common.t_unit in
  FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____1021
let check_pats_for_ite:
  (FStar_Syntax_Syntax.pat* FStar_Syntax_Syntax.term option*
    FStar_Syntax_Syntax.term) Prims.list ->
    (Prims.bool* FStar_Syntax_Syntax.term option* FStar_Syntax_Syntax.term
      option)
  =
  fun l  ->
    let def = (false, None, None) in
    if (FStar_List.length l) <> (Prims.parse_int "2")
    then def
    else
      (let uu____1065 = FStar_List.hd l in
       match uu____1065 with
       | (p1,w1,e1) ->
           let uu____1084 =
             let uu____1089 = FStar_List.tl l in FStar_List.hd uu____1089 in
           (match uu____1084 with
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
                 | uu____1128 -> def)))
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
            let uu____1171 = erasable g f ty in
            if uu____1171
            then
              let uu____1172 =
                type_leq g ty FStar_Extraction_ML_Syntax.ml_unit_ty in
              (if uu____1172
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
          let uu____1188 = type_leq_c g (Some e) ty1 expect in
          match uu____1188 with
          | (true ,Some e') -> e'
          | uu____1194 ->
              (FStar_Extraction_ML_UEnv.debug g
                 (fun uu____1199  ->
                    let uu____1200 =
                      FStar_Extraction_ML_Code.string_of_mlexpr
                        g.FStar_Extraction_ML_UEnv.currentModule e in
                    let uu____1201 =
                      FStar_Extraction_ML_Code.string_of_mlty
                        g.FStar_Extraction_ML_UEnv.currentModule ty1 in
                    let uu____1202 =
                      FStar_Extraction_ML_Code.string_of_mlty
                        g.FStar_Extraction_ML_UEnv.currentModule expect in
                    FStar_Util.print3
                      "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n"
                      uu____1200 uu____1201 uu____1202);
               FStar_All.pipe_left
                 (FStar_Extraction_ML_Syntax.with_ty expect)
                 (FStar_Extraction_ML_Syntax.MLE_Coerce (e, ty1, expect)))
let bv_as_mlty:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlty
  =
  fun g  ->
    fun bv  ->
      let uu____1209 = FStar_Extraction_ML_UEnv.lookup_bv g bv in
      match uu____1209 with
      | FStar_Util.Inl (uu____1210,t) -> t
      | uu____1218 -> FStar_Extraction_ML_Syntax.MLTY_Top
let rec term_as_mlty:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlty
  =
  fun g  ->
    fun t0  ->
      let rec is_top_ty t =
        match t with
        | FStar_Extraction_ML_Syntax.MLTY_Top  -> true
        | FStar_Extraction_ML_Syntax.MLTY_Named uu____1254 ->
            let uu____1258 = FStar_Extraction_ML_Util.udelta_unfold g t in
            (match uu____1258 with | None  -> false | Some t1 -> is_top_ty t1)
        | uu____1261 -> false in
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
      let uu____1264 = is_top_ty mlt in
      if uu____1264
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
      | FStar_Syntax_Syntax.Tm_bvar uu____1270 ->
          let uu____1271 =
            let uu____1272 = FStar_Syntax_Print.term_to_string t1 in
            FStar_Util.format1 "Impossible: Unexpected term %s" uu____1272 in
          failwith uu____1271
      | FStar_Syntax_Syntax.Tm_delayed uu____1273 ->
          let uu____1294 =
            let uu____1295 = FStar_Syntax_Print.term_to_string t1 in
            FStar_Util.format1 "Impossible: Unexpected term %s" uu____1295 in
          failwith uu____1294
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____1296 =
            let uu____1297 = FStar_Syntax_Print.term_to_string t1 in
            FStar_Util.format1 "Impossible: Unexpected term %s" uu____1297 in
          failwith uu____1296
      | FStar_Syntax_Syntax.Tm_constant uu____1298 ->
          FStar_Extraction_ML_UEnv.unknownType
      | FStar_Syntax_Syntax.Tm_uvar uu____1299 ->
          FStar_Extraction_ML_UEnv.unknownType
      | FStar_Syntax_Syntax.Tm_meta (t2,uu____1311) -> term_as_mlty' env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____1316;
             FStar_Syntax_Syntax.index = uu____1317;
             FStar_Syntax_Syntax.sort = t2;_},uu____1319)
          -> term_as_mlty' env t2
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____1327) -> term_as_mlty' env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____1333,uu____1334) ->
          term_as_mlty' env t2
      | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
      | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv []
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____1381 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____1381 with
           | (bs1,c1) ->
               let uu____1386 = binders_as_ml_binders env bs1 in
               (match uu____1386 with
                | (mlbs,env1) ->
                    let t_ret =
                      let eff =
                        FStar_TypeChecker_Env.norm_eff_name
                          env1.FStar_Extraction_ML_UEnv.tcenv
                          (FStar_Syntax_Util.comp_effect_name c1) in
                      let uu____1402 =
                        let uu____1406 =
                          FStar_TypeChecker_Env.effect_decl_opt
                            env1.FStar_Extraction_ML_UEnv.tcenv eff in
                        FStar_Util.must uu____1406 in
                      match uu____1402 with
                      | (ed,qualifiers) ->
                          let uu____1418 =
                            FStar_All.pipe_right qualifiers
                              (FStar_List.contains
                                 FStar_Syntax_Syntax.Reifiable) in
                          if uu____1418
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
                    let uu____1424 =
                      FStar_List.fold_right
                        (fun uu____1431  ->
                           fun uu____1432  ->
                             match (uu____1431, uu____1432) with
                             | ((uu____1443,t2),(tag,t')) ->
                                 (FStar_Extraction_ML_Syntax.E_PURE,
                                   (FStar_Extraction_ML_Syntax.MLTY_Fun
                                      (t2, tag, t')))) mlbs (erase1, t_ret) in
                    (match uu____1424 with | (uu____1451,t2) -> t2)))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let res =
            let uu____1470 =
              let uu____1471 = FStar_Syntax_Util.un_uinst head1 in
              uu____1471.FStar_Syntax_Syntax.n in
            match uu____1470 with
            | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
            | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv args
            | FStar_Syntax_Syntax.Tm_app (head2,args') ->
                let uu____1492 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app
                       (head2, (FStar_List.append args' args))) None
                    t1.FStar_Syntax_Syntax.pos in
                term_as_mlty' env uu____1492
            | uu____1508 -> FStar_Extraction_ML_UEnv.unknownType in
          res
      | FStar_Syntax_Syntax.Tm_abs (bs,ty,uu____1511) ->
          let uu____1534 = FStar_Syntax_Subst.open_term bs ty in
          (match uu____1534 with
           | (bs1,ty1) ->
               let uu____1539 = binders_as_ml_binders env bs1 in
               (match uu____1539 with | (bts,env1) -> term_as_mlty' env1 ty1))
      | FStar_Syntax_Syntax.Tm_type uu____1553 ->
          FStar_Extraction_ML_UEnv.unknownType
      | FStar_Syntax_Syntax.Tm_let uu____1554 ->
          FStar_Extraction_ML_UEnv.unknownType
      | FStar_Syntax_Syntax.Tm_match uu____1562 ->
          FStar_Extraction_ML_UEnv.unknownType
and arg_as_mlty:
  FStar_Extraction_ML_UEnv.env ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.aqual) ->
      FStar_Extraction_ML_Syntax.mlty
  =
  fun g  ->
    fun uu____1578  ->
      match uu____1578 with
      | (a,uu____1582) ->
          let uu____1583 = is_type g a in
          if uu____1583
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
        let uu____1588 =
          let uu____1596 =
            FStar_TypeChecker_Env.lookup_lid g.FStar_Extraction_ML_UEnv.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____1596 with
          | ((uu____1608,ty),uu____1610) ->
              FStar_Syntax_Util.arrow_formals ty in
        match uu____1588 with
        | (formals,t) ->
            let mlargs = FStar_List.map (arg_as_mlty g) args in
            let mlargs1 =
              let n_args = FStar_List.length args in
              if (FStar_List.length formals) > n_args
              then
                let uu____1645 = FStar_Util.first_N n_args formals in
                match uu____1645 with
                | (uu____1659,rest) ->
                    let uu____1673 =
                      FStar_List.map
                        (fun uu____1677  ->
                           FStar_Extraction_ML_UEnv.erasedContent) rest in
                    FStar_List.append mlargs uu____1673
              else mlargs in
            let nm =
              let uu____1682 =
                FStar_Extraction_ML_UEnv.maybe_mangle_type_projector g fv in
              match uu____1682 with
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
      let uu____1693 =
        FStar_All.pipe_right bs
          (FStar_List.fold_left
             (fun uu____1717  ->
                fun b  ->
                  match uu____1717 with
                  | (ml_bs,env) ->
                      let uu____1747 = is_type_binder g b in
                      if uu____1747
                      then
                        let b1 = fst b in
                        let env1 =
                          FStar_Extraction_ML_UEnv.extend_ty env b1
                            (Some FStar_Extraction_ML_Syntax.MLTY_Top) in
                        let ml_b =
                          let uu____1762 =
                            FStar_Extraction_ML_UEnv.bv_as_ml_termvar b1 in
                          (uu____1762, FStar_Extraction_ML_Syntax.ml_unit_ty) in
                        ((ml_b :: ml_bs), env1)
                      else
                        (let b1 = fst b in
                         let t = term_as_mlty env b1.FStar_Syntax_Syntax.sort in
                         let uu____1779 =
                           FStar_Extraction_ML_UEnv.extend_bv env b1 
                             ([], t) false false false in
                         match uu____1779 with
                         | (env1,b2) ->
                             let ml_b =
                               let uu____1797 =
                                 FStar_Extraction_ML_UEnv.removeTick b2 in
                               (uu____1797, t) in
                             ((ml_b :: ml_bs), env1))) ([], g)) in
      match uu____1693 with | (ml_bs,env) -> ((FStar_List.rev ml_bs), env)
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
      | (FStar_Extraction_ML_Syntax.MLE_Seq es1,uu____1857) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (FStar_List.append es1 [e2])
      | (uu____1859,FStar_Extraction_ML_Syntax.MLE_Seq es2) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (e1 :: es2)
      | uu____1862 -> FStar_Extraction_ML_Syntax.MLE_Seq [e1; e2]
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
                    | uu____1884 when
                        (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
                          =
                          FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr
                        -> body.FStar_Extraction_ML_Syntax.expr
                    | uu____1885 ->
                        mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def
                          body)
             | uu____1886 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body))
        | uu____1888 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body)
let resugar_pat:
  FStar_Syntax_Syntax.fv_qual option ->
    FStar_Extraction_ML_Syntax.mlpattern ->
      FStar_Extraction_ML_Syntax.mlpattern
  =
  fun q  ->
    fun p  ->
      match p with
      | FStar_Extraction_ML_Syntax.MLP_CTor (d,pats) ->
          (match FStar_Extraction_ML_Util.is_xtuple d with
           | Some n1 -> FStar_Extraction_ML_Syntax.MLP_Tuple pats
           | uu____1902 ->
               (match q with
                | Some (FStar_Syntax_Syntax.Record_ctor (ty,fns)) ->
                    let path =
                      FStar_List.map FStar_Ident.text_of_id ty.FStar_Ident.ns in
                    let fs = record_fields fns pats in
                    FStar_Extraction_ML_Syntax.MLP_Record (path, fs)
                | uu____1918 -> p))
      | uu____1920 -> p
let rec extract_one_pat:
  Prims.bool ->
    FStar_Extraction_ML_UEnv.env ->
      FStar_Syntax_Syntax.pat ->
        FStar_Extraction_ML_Syntax.mlty option ->
          (FStar_Extraction_ML_UEnv.env*
            (FStar_Extraction_ML_Syntax.mlpattern*
            FStar_Extraction_ML_Syntax.mlexpr Prims.list) option* Prims.bool)
  =
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
                     (fun uu____1956  ->
                        let uu____1957 =
                          FStar_Extraction_ML_Code.string_of_mlty
                            g.FStar_Extraction_ML_UEnv.currentModule t' in
                        let uu____1958 =
                          FStar_Extraction_ML_Code.string_of_mlty
                            g.FStar_Extraction_ML_UEnv.currentModule t in
                        FStar_Util.print2
                          "Expected pattern type %s; got pattern type %s\n"
                          uu____1957 uu____1958)
                 else ();
                 ok) in
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int
              (c,None )) ->
              let i = FStar_Const.Const_int (c, None) in
              let x = FStar_Extraction_ML_Syntax.gensym () in
              let when_clause =
                let uu____1981 =
                  let uu____1982 =
                    let uu____1986 =
                      let uu____1988 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.ml_int_ty)
                          (FStar_Extraction_ML_Syntax.MLE_Var x) in
                      let uu____1989 =
                        let uu____1991 =
                          let uu____1992 =
                            let uu____1993 =
                              FStar_Extraction_ML_Util.mlconst_of_const'
                                p.FStar_Syntax_Syntax.p i in
                            FStar_All.pipe_left
                              (fun _0_31  ->
                                 FStar_Extraction_ML_Syntax.MLE_Const _0_31)
                              uu____1993 in
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty
                               FStar_Extraction_ML_Syntax.ml_int_ty)
                            uu____1992 in
                        [uu____1991] in
                      uu____1988 :: uu____1989 in
                    (FStar_Extraction_ML_Util.prims_op_equality, uu____1986) in
                  FStar_Extraction_ML_Syntax.MLE_App uu____1982 in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     FStar_Extraction_ML_Syntax.ml_bool_ty) uu____1981 in
              let uu____1995 = ok FStar_Extraction_ML_Syntax.ml_int_ty in
              (g,
                (Some ((FStar_Extraction_ML_Syntax.MLP_Var x), [when_clause])),
                uu____1995)
          | FStar_Syntax_Syntax.Pat_constant s ->
              let t =
                FStar_TypeChecker_TcTerm.tc_constant FStar_Range.dummyRange s in
              let mlty = term_as_mlty g t in
              let uu____2007 =
                let uu____2012 =
                  let uu____2016 =
                    let uu____2017 =
                      FStar_Extraction_ML_Util.mlconst_of_const'
                        p.FStar_Syntax_Syntax.p s in
                    FStar_Extraction_ML_Syntax.MLP_Const uu____2017 in
                  (uu____2016, []) in
                Some uu____2012 in
              let uu____2022 = ok mlty in (g, uu____2007, uu____2022)
          | FStar_Syntax_Syntax.Pat_var x ->
              let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort in
              let uu____2029 =
                FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false false
                  imp in
              (match uu____2029 with
               | (g1,x1) ->
                   let uu____2042 = ok mlty in
                   (g1,
                     (if imp
                      then None
                      else Some ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                     uu____2042))
          | FStar_Syntax_Syntax.Pat_wild x ->
              let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort in
              let uu____2061 =
                FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false false
                  imp in
              (match uu____2061 with
               | (g1,x1) ->
                   let uu____2074 = ok mlty in
                   (g1,
                     (if imp
                      then None
                      else Some ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                     uu____2074))
          | FStar_Syntax_Syntax.Pat_dot_term uu____2091 -> (g, None, true)
          | FStar_Syntax_Syntax.Pat_cons (f,pats) ->
              let uu____2113 =
                let uu____2116 = FStar_Extraction_ML_UEnv.lookup_fv g f in
                match uu____2116 with
                | FStar_Util.Inr
                    (uu____2119,{
                                  FStar_Extraction_ML_Syntax.expr =
                                    FStar_Extraction_ML_Syntax.MLE_Name n1;
                                  FStar_Extraction_ML_Syntax.mlty =
                                    uu____2121;
                                  FStar_Extraction_ML_Syntax.loc = uu____2122;_},ttys,uu____2124)
                    -> (n1, ttys)
                | uu____2131 -> failwith "Expected a constructor" in
              (match uu____2113 with
               | (d,tys) ->
                   let nTyVars = FStar_List.length (fst tys) in
                   let uu____2145 = FStar_Util.first_N nTyVars pats in
                   (match uu____2145 with
                    | (tysVarPats,restPats) ->
                        let f_ty_opt =
                          try
                            let mlty_args =
                              FStar_All.pipe_right tysVarPats
                                (FStar_List.map
                                   (fun uu____2210  ->
                                      match uu____2210 with
                                      | (p1,uu____2215) ->
                                          (match p1.FStar_Syntax_Syntax.v
                                           with
                                           | FStar_Syntax_Syntax.Pat_dot_term
                                               (uu____2218,t) ->
                                               term_as_mlty g t
                                           | uu____2224 ->
                                               (FStar_Extraction_ML_UEnv.debug
                                                  g
                                                  (fun uu____2226  ->
                                                     let uu____2227 =
                                                       FStar_Syntax_Print.pat_to_string
                                                         p1 in
                                                     FStar_Util.print1
                                                       "Pattern %s is not extractable"
                                                       uu____2227);
                                                raise Un_extractable)))) in
                            let f_ty =
                              FStar_Extraction_ML_Util.subst tys mlty_args in
                            let uu____2229 =
                              FStar_Extraction_ML_Util.uncurry_mlty_fun f_ty in
                            Some uu____2229
                          with | Un_extractable  -> None in
                        let uu____2244 =
                          FStar_Util.fold_map
                            (fun g1  ->
                               fun uu____2259  ->
                                 match uu____2259 with
                                 | (p1,imp1) ->
                                     let uu____2270 =
                                       extract_one_pat true g1 p1 None in
                                     (match uu____2270 with
                                      | (g2,p2,uu____2286) -> (g2, p2))) g
                            tysVarPats in
                        (match uu____2244 with
                         | (g1,tyMLPats) ->
                             let uu____2318 =
                               FStar_Util.fold_map
                                 (fun uu____2344  ->
                                    fun uu____2345  ->
                                      match (uu____2344, uu____2345) with
                                      | ((g2,f_ty_opt1),(p1,imp1)) ->
                                          let uu____2394 =
                                            match f_ty_opt1 with
                                            | Some (hd1::rest,res) ->
                                                ((Some (rest, res)),
                                                  (Some hd1))
                                            | uu____2426 -> (None, None) in
                                          (match uu____2394 with
                                           | (f_ty_opt2,expected_ty) ->
                                               let uu____2463 =
                                                 extract_one_pat false g2 p1
                                                   expected_ty in
                                               (match uu____2463 with
                                                | (g3,p2,uu____2485) ->
                                                    ((g3, f_ty_opt2), p2))))
                                 (g1, f_ty_opt) restPats in
                             (match uu____2318 with
                              | ((g2,f_ty_opt1),restMLPats) ->
                                  let uu____2546 =
                                    let uu____2552 =
                                      FStar_All.pipe_right
                                        (FStar_List.append tyMLPats
                                           restMLPats)
                                        (FStar_List.collect
                                           (fun uu___137_2577  ->
                                              match uu___137_2577 with
                                              | Some x -> [x]
                                              | uu____2599 -> [])) in
                                    FStar_All.pipe_right uu____2552
                                      FStar_List.split in
                                  (match uu____2546 with
                                   | (mlPats,when_clauses) ->
                                       let pat_ty_compat =
                                         match f_ty_opt1 with
                                         | Some ([],t) -> ok t
                                         | uu____2638 -> false in
                                       let uu____2643 =
                                         let uu____2648 =
                                           let uu____2652 =
                                             resugar_pat
                                               f.FStar_Syntax_Syntax.fv_qual
                                               (FStar_Extraction_ML_Syntax.MLP_CTor
                                                  (d, mlPats)) in
                                           let uu____2654 =
                                             FStar_All.pipe_right
                                               when_clauses
                                               FStar_List.flatten in
                                           (uu____2652, uu____2654) in
                                         Some uu____2648 in
                                       (g2, uu____2643, pat_ty_compat))))))
let extract_pat:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.pat ->
      FStar_Extraction_ML_Syntax.mlty ->
        (FStar_Extraction_ML_UEnv.env* (FStar_Extraction_ML_Syntax.mlpattern*
          FStar_Extraction_ML_Syntax.mlexpr option) Prims.list* Prims.bool)
  =
  fun g  ->
    fun p  ->
      fun expected_t  ->
        let extract_one_pat1 g1 p1 expected_t1 =
          let uu____2708 = extract_one_pat false g1 p1 expected_t1 in
          match uu____2708 with
          | (g2,Some (x,v1),b) -> (g2, (x, v1), b)
          | uu____2739 -> failwith "Impossible: Unable to translate pattern" in
        let mk_when_clause whens =
          match whens with
          | [] -> None
          | hd1::tl1 ->
              let uu____2764 =
                FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd1 tl1 in
              Some uu____2764 in
        let uu____2765 = extract_one_pat1 g p (Some expected_t) in
        match uu____2765 with
        | (g1,(p1,whens),b) ->
            let when_clause = mk_when_clause whens in
            (g1, [(p1, when_clause)], b)
let maybe_eta_data_and_project_record:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.fv_qual option ->
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
            | FStar_Extraction_ML_Syntax.MLTY_Fun (t0,uu____2847,t1) ->
                let x = FStar_Extraction_ML_Syntax.gensym () in
                let uu____2850 =
                  let uu____2856 =
                    let uu____2861 =
                      FStar_All.pipe_left
                        (FStar_Extraction_ML_Syntax.with_ty t0)
                        (FStar_Extraction_ML_Syntax.MLE_Var x) in
                    ((x, t0), uu____2861) in
                  uu____2856 :: more_args in
                eta_args uu____2850 t1
            | FStar_Extraction_ML_Syntax.MLTY_Named (uu____2868,uu____2869)
                -> ((FStar_List.rev more_args), t)
            | uu____2881 -> failwith "Impossible: Head type is not an arrow" in
          let as_record qual1 e =
            match ((e.FStar_Extraction_ML_Syntax.expr), qual1) with
            | (FStar_Extraction_ML_Syntax.MLE_CTor (uu____2899,args),Some
               (FStar_Syntax_Syntax.Record_ctor (tyname,fields))) ->
                let path =
                  FStar_List.map FStar_Ident.text_of_id tyname.FStar_Ident.ns in
                let fields1 = record_fields fields args in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     e.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_Record (path, fields1))
            | uu____2918 -> e in
          let resugar_and_maybe_eta qual1 e =
            let uu____2931 = eta_args [] residualType in
            match uu____2931 with
            | (eargs,tres) ->
                (match eargs with
                 | [] ->
                     let uu____2959 = as_record qual1 e in
                     FStar_Extraction_ML_Util.resugar_exp uu____2959
                 | uu____2960 ->
                     let uu____2966 = FStar_List.unzip eargs in
                     (match uu____2966 with
                      | (binders,eargs1) ->
                          (match e.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_CTor (head1,args)
                               ->
                               let body =
                                 let uu____2990 =
                                   let uu____2991 =
                                     FStar_All.pipe_left
                                       (FStar_Extraction_ML_Syntax.with_ty
                                          tres)
                                       (FStar_Extraction_ML_Syntax.MLE_CTor
                                          (head1,
                                            (FStar_List.append args eargs1))) in
                                   FStar_All.pipe_left (as_record qual1)
                                     uu____2991 in
                                 FStar_All.pipe_left
                                   FStar_Extraction_ML_Util.resugar_exp
                                   uu____2990 in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    e.FStar_Extraction_ML_Syntax.mlty)
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    (binders, body))
                           | uu____2996 ->
                               failwith "Impossible: Not a constructor"))) in
          match ((mlAppExpr.FStar_Extraction_ML_Syntax.expr), qual) with
          | (uu____2998,None ) -> mlAppExpr
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____3001;
                FStar_Extraction_ML_Syntax.loc = uu____3002;_},mle::args),Some
             (FStar_Syntax_Syntax.Record_projector (constrname,f))) ->
              let f1 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append constrname.FStar_Ident.ns [f]) in
              let fn = FStar_Extraction_ML_Util.mlpath_of_lid f1 in
              let proj = FStar_Extraction_ML_Syntax.MLE_Proj (mle, fn) in
              let e =
                match args with
                | [] -> proj
                | uu____3020 ->
                    let uu____3022 =
                      let uu____3026 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj in
                      (uu____3026, args) in
                    FStar_Extraction_ML_Syntax.MLE_App uu____3022 in
              FStar_Extraction_ML_Syntax.with_ty
                mlAppExpr.FStar_Extraction_ML_Syntax.mlty e
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____3029;
                FStar_Extraction_ML_Syntax.loc = uu____3030;_},mlargs),Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____3035 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs)) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____3035
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____3038;
                FStar_Extraction_ML_Syntax.loc = uu____3039;_},mlargs),Some
             (FStar_Syntax_Syntax.Record_ctor uu____3041)) ->
              let uu____3048 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs)) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____3048
          | (FStar_Extraction_ML_Syntax.MLE_Name mlp,Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____3052 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, [])) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____3052
          | (FStar_Extraction_ML_Syntax.MLE_Name mlp,Some
             (FStar_Syntax_Syntax.Record_ctor uu____3055)) ->
              let uu____3060 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, [])) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____3060
          | uu____3062 -> mlAppExpr
let maybe_downgrade_eff:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.e_tag ->
      FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.e_tag
  =
  fun g  ->
    fun f  ->
      fun t  ->
        let uu____3075 =
          (f = FStar_Extraction_ML_Syntax.E_GHOST) &&
            (type_leq g t FStar_Extraction_ML_Syntax.ml_unit_ty) in
        if uu____3075 then FStar_Extraction_ML_Syntax.E_PURE else f
let rec term_as_mlexpr:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Extraction_ML_Syntax.mlexpr* FStar_Extraction_ML_Syntax.e_tag*
        FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun t  ->
      let uu____3116 = term_as_mlexpr' g t in
      match uu____3116 with
      | (e,tag,ty) ->
          let tag1 = maybe_downgrade_eff g tag ty in
          (FStar_Extraction_ML_UEnv.debug g
             (fun u  ->
                let uu____3129 =
                  let uu____3130 = FStar_Syntax_Print.tag_of_term t in
                  let uu____3131 = FStar_Syntax_Print.term_to_string t in
                  let uu____3132 =
                    FStar_Extraction_ML_Code.string_of_mlty
                      g.FStar_Extraction_ML_UEnv.currentModule ty in
                  FStar_Util.format4
                    "term_as_mlexpr (%s) :  %s has ML type %s and effect %s\n"
                    uu____3130 uu____3131 uu____3132
                    (FStar_Extraction_ML_Util.eff_to_string tag1) in
                FStar_Util.print_string uu____3129);
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
          let uu____3139 = check_term_as_mlexpr' g t f ty in
          match uu____3139 with
          | (e,t1) ->
              let uu____3146 = erase g e t1 f in
              (match uu____3146 with | (r,uu____3153,t2) -> (r, t2))
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
          let uu____3161 = term_as_mlexpr g e0 in
          match uu____3161 with
          | (e,tag,t) ->
              let tag1 = maybe_downgrade_eff g tag t in
              if FStar_Extraction_ML_Util.eff_leq tag1 f
              then let uu____3173 = maybe_coerce g e t ty in (uu____3173, ty)
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
           let uu____3184 =
             let uu____3185 =
               FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos in
             let uu____3186 = FStar_Syntax_Print.tag_of_term top in
             let uu____3187 = FStar_Syntax_Print.term_to_string top in
             FStar_Util.format3 "%s: term_as_mlexpr' (%s) :  %s \n"
               uu____3185 uu____3186 uu____3187 in
           FStar_Util.print_string uu____3184);
      (let t = FStar_Syntax_Subst.compress top in
       match t.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____3192 =
             let uu____3193 = FStar_Syntax_Print.tag_of_term t in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____3193 in
           failwith uu____3192
       | FStar_Syntax_Syntax.Tm_delayed uu____3197 ->
           let uu____3218 =
             let uu____3219 = FStar_Syntax_Print.tag_of_term t in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____3219 in
           failwith uu____3218
       | FStar_Syntax_Syntax.Tm_uvar uu____3223 ->
           let uu____3234 =
             let uu____3235 = FStar_Syntax_Print.tag_of_term t in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____3235 in
           failwith uu____3234
       | FStar_Syntax_Syntax.Tm_bvar uu____3239 ->
           let uu____3240 =
             let uu____3241 = FStar_Syntax_Print.tag_of_term t in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____3241 in
           failwith uu____3240
       | FStar_Syntax_Syntax.Tm_type uu____3245 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_refine uu____3246 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_arrow uu____3251 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Mutable_alloc ))
           ->
           let uu____3264 = term_as_mlexpr' g t1 in
           (match uu____3264 with
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
            | uu____3291 -> failwith "impossible")
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_monadic (m,uu____3300)) ->
           let t2 = FStar_Syntax_Subst.compress t1 in
           (match t2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) when
                FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname ->
                let uu____3323 =
                  let uu____3327 =
                    FStar_TypeChecker_Env.effect_decl_opt
                      g.FStar_Extraction_ML_UEnv.tcenv m in
                  FStar_Util.must uu____3327 in
                (match uu____3323 with
                 | (ed,qualifiers) ->
                     let uu____3342 =
                       let uu____3343 =
                         FStar_All.pipe_right qualifiers
                           (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
                       FStar_All.pipe_right uu____3343 Prims.op_Negation in
                     if uu____3342
                     then term_as_mlexpr' g t2
                     else
                       failwith
                         "This should not happen (should have been handled at Tm_abs level)")
            | uu____3352 -> term_as_mlexpr' g t2)
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____3354) -> term_as_mlexpr' g t1
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____3360) -> term_as_mlexpr' g t1
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____3366 =
             FStar_TypeChecker_TcTerm.type_of_tot_term
               g.FStar_Extraction_ML_UEnv.tcenv t in
           (match uu____3366 with
            | (uu____3373,ty,uu____3375) ->
                let ml_ty = term_as_mlty g ty in
                let uu____3377 =
                  let uu____3378 =
                    let uu____3379 =
                      FStar_Extraction_ML_Util.mlconst_of_const'
                        t.FStar_Syntax_Syntax.pos c in
                    FStar_All.pipe_left
                      (fun _0_32  ->
                         FStar_Extraction_ML_Syntax.MLE_Const _0_32)
                      uu____3379 in
                  FStar_Extraction_ML_Syntax.with_ty ml_ty uu____3378 in
                (uu____3377, FStar_Extraction_ML_Syntax.E_PURE, ml_ty))
       | FStar_Syntax_Syntax.Tm_name uu____3380 ->
           let uu____3381 = is_type g t in
           if uu____3381
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____3386 = FStar_Extraction_ML_UEnv.lookup_term g t in
              match uu____3386 with
              | (FStar_Util.Inl uu____3393,uu____3394) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | (FStar_Util.Inr (uu____3413,x,mltys,uu____3416),qual) ->
                  (match mltys with
                   | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                       ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | ([],t1) ->
                       let uu____3441 =
                         maybe_eta_data_and_project_record g qual t1 x in
                       (uu____3441, FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | uu____3442 -> err_uninst g t mltys t))
       | FStar_Syntax_Syntax.Tm_fvar uu____3446 ->
           let uu____3447 = is_type g t in
           if uu____3447
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____3452 = FStar_Extraction_ML_UEnv.lookup_term g t in
              match uu____3452 with
              | (FStar_Util.Inl uu____3459,uu____3460) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | (FStar_Util.Inr (uu____3479,x,mltys,uu____3482),qual) ->
                  (match mltys with
                   | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                       ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | ([],t1) ->
                       let uu____3507 =
                         maybe_eta_data_and_project_record g qual t1 x in
                       (uu____3507, FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | uu____3508 -> err_uninst g t mltys t))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,copt) ->
           let uu____3537 = FStar_Syntax_Subst.open_term bs body in
           (match uu____3537 with
            | (bs1,body1) ->
                let uu____3545 = binders_as_ml_binders g bs1 in
                (match uu____3545 with
                 | (ml_bs,env) ->
                     let body2 =
                       match copt with
                       | Some c ->
                           (FStar_Extraction_ML_UEnv.debug g
                              (fun uu____3575  ->
                                 match c with
                                 | FStar_Util.Inl lc ->
                                     let uu____3580 =
                                       FStar_Syntax_Print.lcomp_to_string lc in
                                     FStar_Util.print1 "Computation lc: %s\n"
                                       uu____3580
                                 | FStar_Util.Inr rc ->
                                     FStar_Util.print1 "Computation rc: %s\n"
                                       (FStar_Ident.text_of_lid (fst rc)));
                            (let uu____3589 =
                               FStar_TypeChecker_Env.is_reifiable
                                 env.FStar_Extraction_ML_UEnv.tcenv c in
                             if uu____3589
                             then
                               FStar_TypeChecker_Util.reify_body
                                 env.FStar_Extraction_ML_UEnv.tcenv body1
                             else body1))
                       | None  ->
                           (FStar_Extraction_ML_UEnv.debug g
                              (fun uu____3597  ->
                                 let uu____3598 =
                                   FStar_Syntax_Print.term_to_string body1 in
                                 FStar_Util.print1
                                   "No computation type for: %s\n" uu____3598);
                            body1) in
                     let uu____3599 = term_as_mlexpr env body2 in
                     (match uu____3599 with
                      | (ml_body,f,t1) ->
                          let uu____3609 =
                            FStar_List.fold_right
                              (fun uu____3616  ->
                                 fun uu____3617  ->
                                   match (uu____3616, uu____3617) with
                                   | ((uu____3628,targ),(f1,t2)) ->
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         (FStar_Extraction_ML_Syntax.MLTY_Fun
                                            (targ, f1, t2)))) ml_bs (f, t1) in
                          (match uu____3609 with
                           | (f1,tfun) ->
                               let uu____3641 =
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty tfun)
                                   (FStar_Extraction_ML_Syntax.MLE_Fun
                                      (ml_bs, ml_body)) in
                               (uu____3641, f1, tfun)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____3645);
              FStar_Syntax_Syntax.tk = uu____3646;
              FStar_Syntax_Syntax.pos = uu____3647;
              FStar_Syntax_Syntax.vars = uu____3648;_},uu____3649)
           -> failwith "Unreachable? Tm_app Const_reflect"
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let is_total uu___139_3691 =
             match uu___139_3691 with
             | FStar_Util.Inl l -> FStar_Syntax_Util.is_total_lcomp l
             | FStar_Util.Inr (l,flags) ->
                 (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid)
                   ||
                   (FStar_All.pipe_right flags
                      (FStar_List.existsb
                         (fun uu___138_3709  ->
                            match uu___138_3709 with
                            | FStar_Syntax_Syntax.TOTAL  -> true
                            | uu____3710 -> false))) in
           let uu____3711 =
             let uu____3714 =
               let uu____3715 = FStar_Syntax_Subst.compress head1 in
               uu____3715.FStar_Syntax_Syntax.n in
             ((head1.FStar_Syntax_Syntax.n), uu____3714) in
           (match uu____3711 with
            | (FStar_Syntax_Syntax.Tm_uvar uu____3721,uu____3722) ->
                let t1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.Iota;
                    FStar_TypeChecker_Normalize.Zeta;
                    FStar_TypeChecker_Normalize.EraseUniverses;
                    FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                    g.FStar_Extraction_ML_UEnv.tcenv t in
                term_as_mlexpr' g t1
            | (uu____3734,FStar_Syntax_Syntax.Tm_abs (bs,uu____3736,Some lc))
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
            | (uu____3765,FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_reify )) ->
                let e =
                  let uu____3767 = FStar_List.hd args in
                  FStar_TypeChecker_Util.reify_body_with_arg
                    g.FStar_Extraction_ML_UEnv.tcenv head1 uu____3767 in
                let tm =
                  let uu____3775 =
                    let uu____3776 = FStar_TypeChecker_Util.remove_reify e in
                    let uu____3777 = FStar_List.tl args in
                    FStar_Syntax_Syntax.mk_Tm_app uu____3776 uu____3777 in
                  uu____3775 None t.FStar_Syntax_Syntax.pos in
                term_as_mlexpr' g tm
            | uu____3786 ->
                let rec extract_app is_data uu____3814 uu____3815 restArgs =
                  match (uu____3814, uu____3815) with
                  | ((mlhead,mlargs_f),(f,t1)) ->
                      (match (restArgs, t1) with
                       | ([],uu____3863) ->
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
                                | uu____3877 -> false) in
                           let uu____3878 =
                             if evaluation_order_guaranteed
                             then
                               let uu____3891 =
                                 FStar_All.pipe_right
                                   (FStar_List.rev mlargs_f)
                                   (FStar_List.map FStar_Pervasives.fst) in
                               ([], uu____3891)
                             else
                               FStar_List.fold_left
                                 (fun uu____3916  ->
                                    fun uu____3917  ->
                                      match (uu____3916, uu____3917) with
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
                                             let uu____3972 =
                                               let uu____3974 =
                                                 FStar_All.pipe_left
                                                   (FStar_Extraction_ML_Syntax.with_ty
                                                      arg.FStar_Extraction_ML_Syntax.mlty)
                                                   (FStar_Extraction_ML_Syntax.MLE_Var
                                                      x) in
                                               uu____3974 :: out_args in
                                             (((x, arg) :: lbs), uu____3972)))
                                 ([], []) mlargs_f in
                           (match uu____3878 with
                            | (lbs,mlargs) ->
                                let app =
                                  let uu____4001 =
                                    FStar_All.pipe_left
                                      (FStar_Extraction_ML_Syntax.with_ty t1)
                                      (FStar_Extraction_ML_Syntax.MLE_App
                                         (mlhead, mlargs)) in
                                  FStar_All.pipe_left
                                    (maybe_eta_data_and_project_record g
                                       is_data t1) uu____4001 in
                                let l_app =
                                  FStar_List.fold_right
                                    (fun uu____4006  ->
                                       fun out  ->
                                         match uu____4006 with
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
                       | ((arg,uu____4019)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                          (formal_t,f',t2)) when
                           (is_type g arg) &&
                             (type_leq g formal_t
                                FStar_Extraction_ML_Syntax.ml_unit_ty)
                           ->
                           let uu____4037 =
                             let uu____4040 =
                               FStar_Extraction_ML_Util.join
                                 arg.FStar_Syntax_Syntax.pos f f' in
                             (uu____4040, t2) in
                           extract_app is_data
                             (mlhead,
                               ((FStar_Extraction_ML_Syntax.ml_unit,
                                  FStar_Extraction_ML_Syntax.E_PURE) ::
                               mlargs_f)) uu____4037 rest
                       | ((e0,uu____4047)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                          (tExpected,f',t2)) ->
                           let r = e0.FStar_Syntax_Syntax.pos in
                           let uu____4066 = term_as_mlexpr g e0 in
                           (match uu____4066 with
                            | (e01,f0,tInferred) ->
                                let e02 =
                                  maybe_coerce g e01 tInferred tExpected in
                                let uu____4077 =
                                  let uu____4080 =
                                    FStar_Extraction_ML_Util.join_l r
                                      [f; f'; f0] in
                                  (uu____4080, t2) in
                                extract_app is_data
                                  (mlhead, ((e02, f0) :: mlargs_f))
                                  uu____4077 rest)
                       | uu____4086 ->
                           let uu____4093 =
                             FStar_Extraction_ML_Util.udelta_unfold g t1 in
                           (match uu____4093 with
                            | Some t2 ->
                                extract_app is_data (mlhead, mlargs_f)
                                  (f, t2) restArgs
                            | None  ->
                                err_ill_typed_application g top restArgs t1)) in
                let extract_app_maybe_projector is_data mlhead uu____4129
                  args1 =
                  match uu____4129 with
                  | (f,t1) ->
                      (match is_data with
                       | Some (FStar_Syntax_Syntax.Record_projector
                           uu____4148) ->
                           let rec remove_implicits args2 f1 t2 =
                             match (args2, t2) with
                             | ((a0,Some (FStar_Syntax_Syntax.Implicit
                                 uu____4198))::args3,FStar_Extraction_ML_Syntax.MLTY_Fun
                                (uu____4200,f',t3)) ->
                                 let uu____4225 =
                                   FStar_Extraction_ML_Util.join
                                     a0.FStar_Syntax_Syntax.pos f1 f' in
                                 remove_implicits args3 uu____4225 t3
                             | uu____4226 -> (args2, f1, t2) in
                           let uu____4241 = remove_implicits args1 f t1 in
                           (match uu____4241 with
                            | (args2,f1,t2) ->
                                extract_app is_data (mlhead, []) (f1, t2)
                                  args2)
                       | uu____4274 ->
                           extract_app is_data (mlhead, []) (f, t1) args1) in
                let uu____4281 = is_type g t in
                if uu____4281
                then
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
                else
                  (let head2 = FStar_Syntax_Util.un_uinst head1 in
                   match head2.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_name uu____4290 ->
                       let uu____4291 =
                         let uu____4298 =
                           FStar_Extraction_ML_UEnv.lookup_term g head2 in
                         match uu____4298 with
                         | (FStar_Util.Inr (uu____4308,x1,x2,x3),q) ->
                             ((x1, x2, x3), q)
                         | uu____4333 -> failwith "FIXME Ty" in
                       (match uu____4291 with
                        | ((head_ml,(vars,t1),inst_ok),qual) ->
                            let has_typ_apps =
                              match args with
                              | (a,uu____4362)::uu____4363 -> is_type g a
                              | uu____4377 -> false in
                            let uu____4383 =
                              match vars with
                              | uu____4400::uu____4401 when
                                  (Prims.op_Negation has_typ_apps) && inst_ok
                                  -> (head_ml, t1, args)
                              | uu____4408 ->
                                  let n1 = FStar_List.length vars in
                                  if n1 <= (FStar_List.length args)
                                  then
                                    let uu____4428 =
                                      FStar_Util.first_N n1 args in
                                    (match uu____4428 with
                                     | (prefix1,rest) ->
                                         let prefixAsMLTypes =
                                           FStar_List.map
                                             (fun uu____4481  ->
                                                match uu____4481 with
                                                | (x,uu____4485) ->
                                                    term_as_mlty g x) prefix1 in
                                         let t2 =
                                           instantiate (vars, t1)
                                             prefixAsMLTypes in
                                         let head3 =
                                           match head_ml.FStar_Extraction_ML_Syntax.expr
                                           with
                                           | FStar_Extraction_ML_Syntax.MLE_Name
                                               uu____4488 ->
                                               let uu___143_4489 = head_ml in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (uu___143_4489.FStar_Extraction_ML_Syntax.expr);
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   = t2;
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___143_4489.FStar_Extraction_ML_Syntax.loc)
                                               }
                                           | FStar_Extraction_ML_Syntax.MLE_Var
                                               uu____4490 ->
                                               let uu___143_4491 = head_ml in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (uu___143_4491.FStar_Extraction_ML_Syntax.expr);
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   = t2;
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___143_4491.FStar_Extraction_ML_Syntax.loc)
                                               }
                                           | FStar_Extraction_ML_Syntax.MLE_App
                                               (head3,{
                                                        FStar_Extraction_ML_Syntax.expr
                                                          =
                                                          FStar_Extraction_ML_Syntax.MLE_Const
                                                          (FStar_Extraction_ML_Syntax.MLC_Unit
                                                          );
                                                        FStar_Extraction_ML_Syntax.mlty
                                                          = uu____4493;
                                                        FStar_Extraction_ML_Syntax.loc
                                                          = uu____4494;_}::[])
                                               ->
                                               FStar_All.pipe_right
                                                 (FStar_Extraction_ML_Syntax.MLE_App
                                                    ((let uu___144_4497 =
                                                        head3 in
                                                      {
                                                        FStar_Extraction_ML_Syntax.expr
                                                          =
                                                          (uu___144_4497.FStar_Extraction_ML_Syntax.expr);
                                                        FStar_Extraction_ML_Syntax.mlty
                                                          =
                                                          (FStar_Extraction_ML_Syntax.MLTY_Fun
                                                             (FStar_Extraction_ML_Syntax.ml_unit_ty,
                                                               FStar_Extraction_ML_Syntax.E_PURE,
                                                               t2));
                                                        FStar_Extraction_ML_Syntax.loc
                                                          =
                                                          (uu___144_4497.FStar_Extraction_ML_Syntax.loc)
                                                      }),
                                                      [FStar_Extraction_ML_Syntax.ml_unit]))
                                                 (FStar_Extraction_ML_Syntax.with_ty
                                                    t2)
                                           | uu____4498 ->
                                               failwith
                                                 "Impossible: Unexpected head term" in
                                         (head3, t2, rest))
                                  else err_uninst g head2 (vars, t1) top in
                            (match uu____4383 with
                             | (head_ml1,head_t,args1) ->
                                 (match args1 with
                                  | [] ->
                                      let uu____4536 =
                                        maybe_eta_data_and_project_record g
                                          qual head_t head_ml1 in
                                      (uu____4536,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        head_t)
                                  | uu____4537 ->
                                      extract_app_maybe_projector qual
                                        head_ml1
                                        (FStar_Extraction_ML_Syntax.E_PURE,
                                          head_t) args1)))
                   | FStar_Syntax_Syntax.Tm_fvar uu____4543 ->
                       let uu____4544 =
                         let uu____4551 =
                           FStar_Extraction_ML_UEnv.lookup_term g head2 in
                         match uu____4551 with
                         | (FStar_Util.Inr (uu____4561,x1,x2,x3),q) ->
                             ((x1, x2, x3), q)
                         | uu____4586 -> failwith "FIXME Ty" in
                       (match uu____4544 with
                        | ((head_ml,(vars,t1),inst_ok),qual) ->
                            let has_typ_apps =
                              match args with
                              | (a,uu____4615)::uu____4616 -> is_type g a
                              | uu____4630 -> false in
                            let uu____4636 =
                              match vars with
                              | uu____4653::uu____4654 when
                                  (Prims.op_Negation has_typ_apps) && inst_ok
                                  -> (head_ml, t1, args)
                              | uu____4661 ->
                                  let n1 = FStar_List.length vars in
                                  if n1 <= (FStar_List.length args)
                                  then
                                    let uu____4681 =
                                      FStar_Util.first_N n1 args in
                                    (match uu____4681 with
                                     | (prefix1,rest) ->
                                         let prefixAsMLTypes =
                                           FStar_List.map
                                             (fun uu____4734  ->
                                                match uu____4734 with
                                                | (x,uu____4738) ->
                                                    term_as_mlty g x) prefix1 in
                                         let t2 =
                                           instantiate (vars, t1)
                                             prefixAsMLTypes in
                                         let head3 =
                                           match head_ml.FStar_Extraction_ML_Syntax.expr
                                           with
                                           | FStar_Extraction_ML_Syntax.MLE_Name
                                               uu____4741 ->
                                               let uu___143_4742 = head_ml in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (uu___143_4742.FStar_Extraction_ML_Syntax.expr);
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   = t2;
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___143_4742.FStar_Extraction_ML_Syntax.loc)
                                               }
                                           | FStar_Extraction_ML_Syntax.MLE_Var
                                               uu____4743 ->
                                               let uu___143_4744 = head_ml in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (uu___143_4744.FStar_Extraction_ML_Syntax.expr);
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   = t2;
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___143_4744.FStar_Extraction_ML_Syntax.loc)
                                               }
                                           | FStar_Extraction_ML_Syntax.MLE_App
                                               (head3,{
                                                        FStar_Extraction_ML_Syntax.expr
                                                          =
                                                          FStar_Extraction_ML_Syntax.MLE_Const
                                                          (FStar_Extraction_ML_Syntax.MLC_Unit
                                                          );
                                                        FStar_Extraction_ML_Syntax.mlty
                                                          = uu____4746;
                                                        FStar_Extraction_ML_Syntax.loc
                                                          = uu____4747;_}::[])
                                               ->
                                               FStar_All.pipe_right
                                                 (FStar_Extraction_ML_Syntax.MLE_App
                                                    ((let uu___144_4750 =
                                                        head3 in
                                                      {
                                                        FStar_Extraction_ML_Syntax.expr
                                                          =
                                                          (uu___144_4750.FStar_Extraction_ML_Syntax.expr);
                                                        FStar_Extraction_ML_Syntax.mlty
                                                          =
                                                          (FStar_Extraction_ML_Syntax.MLTY_Fun
                                                             (FStar_Extraction_ML_Syntax.ml_unit_ty,
                                                               FStar_Extraction_ML_Syntax.E_PURE,
                                                               t2));
                                                        FStar_Extraction_ML_Syntax.loc
                                                          =
                                                          (uu___144_4750.FStar_Extraction_ML_Syntax.loc)
                                                      }),
                                                      [FStar_Extraction_ML_Syntax.ml_unit]))
                                                 (FStar_Extraction_ML_Syntax.with_ty
                                                    t2)
                                           | uu____4751 ->
                                               failwith
                                                 "Impossible: Unexpected head term" in
                                         (head3, t2, rest))
                                  else err_uninst g head2 (vars, t1) top in
                            (match uu____4636 with
                             | (head_ml1,head_t,args1) ->
                                 (match args1 with
                                  | [] ->
                                      let uu____4789 =
                                        maybe_eta_data_and_project_record g
                                          qual head_t head_ml1 in
                                      (uu____4789,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        head_t)
                                  | uu____4790 ->
                                      extract_app_maybe_projector qual
                                        head_ml1
                                        (FStar_Extraction_ML_Syntax.E_PURE,
                                          head_t) args1)))
                   | uu____4796 ->
                       let uu____4797 = term_as_mlexpr g head2 in
                       (match uu____4797 with
                        | (head3,f,t1) ->
                            extract_app_maybe_projector None head3 (f, t1)
                              args)))
       | FStar_Syntax_Syntax.Tm_ascribed (e0,(tc,uu____4809),f) ->
           let t1 =
             match tc with
             | FStar_Util.Inl t1 -> term_as_mlty g t1
             | FStar_Util.Inr c ->
                 term_as_mlty g (FStar_Syntax_Util.comp_result c) in
           let f1 =
             match f with
             | None  -> failwith "Ascription node with an empty effect label"
             | Some l -> effect_as_etag g l in
           let uu____4863 = check_term_as_mlexpr g e0 f1 t1 in
           (match uu____4863 with | (e,t2) -> (e, f1, t2))
       | FStar_Syntax_Syntax.Tm_let ((is_rec,lbs),e') ->
           let top_level = FStar_Syntax_Syntax.is_top_level lbs in
           let uu____4884 =
             if is_rec
             then FStar_Syntax_Subst.open_let_rec lbs e'
             else
               (let uu____4892 = FStar_Syntax_Syntax.is_top_level lbs in
                if uu____4892
                then (lbs, e')
                else
                  (let lb = FStar_List.hd lbs in
                   let x =
                     let uu____4902 =
                       FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                     FStar_Syntax_Syntax.freshen_bv uu____4902 in
                   let lb1 =
                     let uu___145_4904 = lb in
                     {
                       FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                       FStar_Syntax_Syntax.lbunivs =
                         (uu___145_4904.FStar_Syntax_Syntax.lbunivs);
                       FStar_Syntax_Syntax.lbtyp =
                         (uu___145_4904.FStar_Syntax_Syntax.lbtyp);
                       FStar_Syntax_Syntax.lbeff =
                         (uu___145_4904.FStar_Syntax_Syntax.lbeff);
                       FStar_Syntax_Syntax.lbdef =
                         (uu___145_4904.FStar_Syntax_Syntax.lbdef)
                     } in
                   let e'1 =
                     FStar_Syntax_Subst.subst
                       [FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x)] e' in
                   ([lb1], e'1))) in
           (match uu____4884 with
            | (lbs1,e'1) ->
                let lbs2 =
                  if top_level
                  then
                    FStar_All.pipe_right lbs1
                      (FStar_List.map
                         (fun lb  ->
                            let tcenv =
                              let uu____4921 =
                                FStar_Ident.lid_of_path
                                  (FStar_List.append
                                     (fst
                                        g.FStar_Extraction_ML_UEnv.currentModule)
                                     [snd
                                        g.FStar_Extraction_ML_UEnv.currentModule])
                                  FStar_Range.dummyRange in
                              FStar_TypeChecker_Env.set_current_module
                                g.FStar_Extraction_ML_UEnv.tcenv uu____4921 in
                            FStar_Extraction_ML_UEnv.debug g
                              (fun uu____4925  ->
                                 FStar_Options.set_option "debug_level"
                                   (FStar_Options.List
                                      [FStar_Options.String "Norm";
                                      FStar_Options.String "Extraction"]));
                            (let lbdef =
                               let uu____4929 = FStar_Options.ml_ish () in
                               if uu____4929
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
                             let uu___146_4933 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___146_4933.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___146_4933.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___146_4933.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___146_4933.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef
                             })))
                  else lbs1 in
                let maybe_generalize uu____4947 =
                  match uu____4947 with
                  | { FStar_Syntax_Syntax.lbname = lbname_;
                      FStar_Syntax_Syntax.lbunivs = uu____4958;
                      FStar_Syntax_Syntax.lbtyp = t1;
                      FStar_Syntax_Syntax.lbeff = lbeff;
                      FStar_Syntax_Syntax.lbdef = e;_} ->
                      let f_e = effect_as_etag g lbeff in
                      let t2 = FStar_Syntax_Subst.compress t1 in
                      (match t2.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                           let uu____5001 = FStar_List.hd bs in
                           FStar_All.pipe_right uu____5001 (is_type_binder g)
                           ->
                           let uu____5008 = FStar_Syntax_Subst.open_comp bs c in
                           (match uu____5008 with
                            | (bs1,c1) ->
                                let uu____5022 =
                                  let uu____5027 =
                                    FStar_Util.prefix_until
                                      (fun x  ->
                                         let uu____5045 = is_type_binder g x in
                                         Prims.op_Negation uu____5045) bs1 in
                                  match uu____5027 with
                                  | None  ->
                                      (bs1,
                                        (FStar_Syntax_Util.comp_result c1))
                                  | Some (bs2,b,rest) ->
                                      let uu____5093 =
                                        FStar_Syntax_Util.arrow (b :: rest)
                                          c1 in
                                      (bs2, uu____5093) in
                                (match uu____5022 with
                                 | (tbinders,tbody) ->
                                     let n_tbinders =
                                       FStar_List.length tbinders in
                                     let e1 =
                                       let uu____5123 = normalize_abs e in
                                       FStar_All.pipe_right uu____5123
                                         FStar_Syntax_Util.unmeta in
                                     (match e1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Tm_abs
                                          (bs2,body,copt) ->
                                          let uu____5158 =
                                            FStar_Syntax_Subst.open_term bs2
                                              body in
                                          (match uu____5158 with
                                           | (bs3,body1) ->
                                               if
                                                 n_tbinders <=
                                                   (FStar_List.length bs3)
                                               then
                                                 let uu____5188 =
                                                   FStar_Util.first_N
                                                     n_tbinders bs3 in
                                                 (match uu____5188 with
                                                  | (targs,rest_args) ->
                                                      let expected_source_ty
                                                        =
                                                        let s =
                                                          FStar_List.map2
                                                            (fun uu____5231 
                                                               ->
                                                               fun uu____5232
                                                                  ->
                                                                 match 
                                                                   (uu____5231,
                                                                    uu____5232)
                                                                 with
                                                                 | ((x,uu____5242),
                                                                    (y,uu____5244))
                                                                    ->
                                                                    let uu____5249
                                                                    =
                                                                    let uu____5254
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    y in
                                                                    (x,
                                                                    uu____5254) in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____5249)
                                                            tbinders targs in
                                                        FStar_Syntax_Subst.subst
                                                          s tbody in
                                                      let env =
                                                        FStar_List.fold_left
                                                          (fun env  ->
                                                             fun uu____5259 
                                                               ->
                                                               match uu____5259
                                                               with
                                                               | (a,uu____5263)
                                                                   ->
                                                                   FStar_Extraction_ML_UEnv.extend_ty
                                                                    env a
                                                                    None) g
                                                          targs in
                                                      let expected_t =
                                                        term_as_mlty env
                                                          expected_source_ty in
                                                      let polytype =
                                                        let uu____5271 =
                                                          FStar_All.pipe_right
                                                            targs
                                                            (FStar_List.map
                                                               (fun
                                                                  uu____5285 
                                                                  ->
                                                                  match uu____5285
                                                                  with
                                                                  | (x,uu____5291)
                                                                    ->
                                                                    FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                                    x)) in
                                                        (uu____5271,
                                                          expected_t) in
                                                      let add_unit =
                                                        match rest_args with
                                                        | [] ->
                                                            let uu____5298 =
                                                              is_fstar_value
                                                                body1 in
                                                            Prims.op_Negation
                                                              uu____5298
                                                        | uu____5299 -> false in
                                                      let rest_args1 =
                                                        if add_unit
                                                        then unit_binder ::
                                                          rest_args
                                                        else rest_args in
                                                      let body2 =
                                                        match rest_args1 with
                                                        | [] -> body1
                                                        | uu____5308 ->
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
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          uu____5352 ->
                                          let env =
                                            FStar_List.fold_left
                                              (fun env  ->
                                                 fun uu____5361  ->
                                                   match uu____5361 with
                                                   | (a,uu____5365) ->
                                                       FStar_Extraction_ML_UEnv.extend_ty
                                                         env a None) g
                                              tbinders in
                                          let expected_t =
                                            term_as_mlty env tbody in
                                          let polytype =
                                            let uu____5373 =
                                              FStar_All.pipe_right tbinders
                                                (FStar_List.map
                                                   (fun uu____5384  ->
                                                      match uu____5384 with
                                                      | (x,uu____5390) ->
                                                          FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                            x)) in
                                            (uu____5373, expected_t) in
                                          let args =
                                            FStar_All.pipe_right tbinders
                                              (FStar_List.map
                                                 (fun uu____5399  ->
                                                    match uu____5399 with
                                                    | (bv,uu____5403) ->
                                                        let uu____5404 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            bv in
                                                        FStar_All.pipe_right
                                                          uu____5404
                                                          FStar_Syntax_Syntax.as_arg)) in
                                          let e2 =
                                            FStar_Syntax_Syntax.mk
                                              (FStar_Syntax_Syntax.Tm_app
                                                 (e1, args)) None
                                              e1.FStar_Syntax_Syntax.pos in
                                          (lbname_, f_e,
                                            (t2, (tbinders, polytype)),
                                            false, e2)
                                      | FStar_Syntax_Syntax.Tm_fvar
                                          uu____5438 ->
                                          let env =
                                            FStar_List.fold_left
                                              (fun env  ->
                                                 fun uu____5443  ->
                                                   match uu____5443 with
                                                   | (a,uu____5447) ->
                                                       FStar_Extraction_ML_UEnv.extend_ty
                                                         env a None) g
                                              tbinders in
                                          let expected_t =
                                            term_as_mlty env tbody in
                                          let polytype =
                                            let uu____5455 =
                                              FStar_All.pipe_right tbinders
                                                (FStar_List.map
                                                   (fun uu____5466  ->
                                                      match uu____5466 with
                                                      | (x,uu____5472) ->
                                                          FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                            x)) in
                                            (uu____5455, expected_t) in
                                          let args =
                                            FStar_All.pipe_right tbinders
                                              (FStar_List.map
                                                 (fun uu____5481  ->
                                                    match uu____5481 with
                                                    | (bv,uu____5485) ->
                                                        let uu____5486 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            bv in
                                                        FStar_All.pipe_right
                                                          uu____5486
                                                          FStar_Syntax_Syntax.as_arg)) in
                                          let e2 =
                                            FStar_Syntax_Syntax.mk
                                              (FStar_Syntax_Syntax.Tm_app
                                                 (e1, args)) None
                                              e1.FStar_Syntax_Syntax.pos in
                                          (lbname_, f_e,
                                            (t2, (tbinders, polytype)),
                                            false, e2)
                                      | FStar_Syntax_Syntax.Tm_name
                                          uu____5520 ->
                                          let env =
                                            FStar_List.fold_left
                                              (fun env  ->
                                                 fun uu____5525  ->
                                                   match uu____5525 with
                                                   | (a,uu____5529) ->
                                                       FStar_Extraction_ML_UEnv.extend_ty
                                                         env a None) g
                                              tbinders in
                                          let expected_t =
                                            term_as_mlty env tbody in
                                          let polytype =
                                            let uu____5537 =
                                              FStar_All.pipe_right tbinders
                                                (FStar_List.map
                                                   (fun uu____5548  ->
                                                      match uu____5548 with
                                                      | (x,uu____5554) ->
                                                          FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                            x)) in
                                            (uu____5537, expected_t) in
                                          let args =
                                            FStar_All.pipe_right tbinders
                                              (FStar_List.map
                                                 (fun uu____5563  ->
                                                    match uu____5563 with
                                                    | (bv,uu____5567) ->
                                                        let uu____5568 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            bv in
                                                        FStar_All.pipe_right
                                                          uu____5568
                                                          FStar_Syntax_Syntax.as_arg)) in
                                          let e2 =
                                            FStar_Syntax_Syntax.mk
                                              (FStar_Syntax_Syntax.Tm_app
                                                 (e1, args)) None
                                              e1.FStar_Syntax_Syntax.pos in
                                          (lbname_, f_e,
                                            (t2, (tbinders, polytype)),
                                            false, e2)
                                      | uu____5602 ->
                                          err_value_restriction e1)))
                       | uu____5612 ->
                           let expected_t = term_as_mlty g t2 in
                           (lbname_, f_e, (t2, ([], ([], expected_t))),
                             false, e)) in
                let check_lb env uu____5669 =
                  match uu____5669 with
                  | (nm,(lbname,f,(t1,(targs,polytype)),add_unit,e)) ->
                      let env1 =
                        FStar_List.fold_left
                          (fun env1  ->
                             fun uu____5740  ->
                               match uu____5740 with
                               | (a,uu____5744) ->
                                   FStar_Extraction_ML_UEnv.extend_ty env1 a
                                     None) env targs in
                      let expected_t =
                        if add_unit
                        then
                          FStar_Extraction_ML_Syntax.MLTY_Fun
                            (FStar_Extraction_ML_Syntax.ml_unit_ty,
                              FStar_Extraction_ML_Syntax.E_PURE,
                              (snd polytype))
                        else snd polytype in
                      let uu____5747 =
                        check_term_as_mlexpr env1 e f expected_t in
                      (match uu____5747 with
                       | (e1,uu____5753) ->
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
                let uu____5788 =
                  FStar_List.fold_right
                    (fun lb  ->
                       fun uu____5827  ->
                         match uu____5827 with
                         | (env,lbs4) ->
                             let uu____5891 = lb in
                             (match uu____5891 with
                              | (lbname,uu____5916,(t1,(uu____5918,polytype)),add_unit,uu____5921)
                                  ->
                                  let uu____5928 =
                                    FStar_Extraction_ML_UEnv.extend_lb env
                                      lbname t1 polytype add_unit true in
                                  (match uu____5928 with
                                   | (env1,nm) -> (env1, ((nm, lb) :: lbs4)))))
                    lbs3 (g, []) in
                (match uu____5788 with
                 | (env_body,lbs4) ->
                     let env_def = if is_rec then env_body else g in
                     let lbs5 =
                       FStar_All.pipe_right lbs4
                         (FStar_List.map (check_lb env_def)) in
                     let e'_rng = e'1.FStar_Syntax_Syntax.pos in
                     let uu____6071 = term_as_mlexpr env_body e'1 in
                     (match uu____6071 with
                      | (e'2,f',t') ->
                          let f =
                            let uu____6082 =
                              let uu____6084 =
                                FStar_List.map FStar_Pervasives.fst lbs5 in
                              f' :: uu____6084 in
                            FStar_Extraction_ML_Util.join_l e'_rng uu____6082 in
                          let is_rec1 =
                            if is_rec = true
                            then FStar_Extraction_ML_Syntax.Rec
                            else FStar_Extraction_ML_Syntax.NonRec in
                          let uu____6090 =
                            let uu____6091 =
                              let uu____6092 =
                                let uu____6093 =
                                  FStar_List.map FStar_Pervasives.snd lbs5 in
                                (is_rec1, [], uu____6093) in
                              mk_MLE_Let top_level uu____6092 e'2 in
                            let uu____6099 =
                              FStar_Extraction_ML_Util.mlloc_of_range
                                t.FStar_Syntax_Syntax.pos in
                            FStar_Extraction_ML_Syntax.with_ty_loc t'
                              uu____6091 uu____6099 in
                          (uu____6090, f, t'))))
       | FStar_Syntax_Syntax.Tm_match (scrutinee,pats) ->
           let uu____6126 = term_as_mlexpr g scrutinee in
           (match uu____6126 with
            | (e,f_e,t_e) ->
                let uu____6136 = check_pats_for_ite pats in
                (match uu____6136 with
                 | (b,then_e,else_e) ->
                     let no_lift x t1 = x in
                     if b
                     then
                       (match (then_e, else_e) with
                        | (Some then_e1,Some else_e1) ->
                            let uu____6171 = term_as_mlexpr g then_e1 in
                            (match uu____6171 with
                             | (then_mle,f_then,t_then) ->
                                 let uu____6181 = term_as_mlexpr g else_e1 in
                                 (match uu____6181 with
                                  | (else_mle,f_else,t_else) ->
                                      let uu____6191 =
                                        let uu____6198 =
                                          type_leq g t_then t_else in
                                        if uu____6198
                                        then (t_else, no_lift)
                                        else
                                          (let uu____6210 =
                                             type_leq g t_else t_then in
                                           if uu____6210
                                           then (t_then, no_lift)
                                           else
                                             (FStar_Extraction_ML_Syntax.MLTY_Top,
                                               FStar_Extraction_ML_Syntax.apply_obj_repr)) in
                                      (match uu____6191 with
                                       | (t_branch,maybe_lift1) ->
                                           let uu____6239 =
                                             let uu____6240 =
                                               let uu____6241 =
                                                 let uu____6246 =
                                                   maybe_lift1 then_mle
                                                     t_then in
                                                 let uu____6247 =
                                                   let uu____6249 =
                                                     maybe_lift1 else_mle
                                                       t_else in
                                                   Some uu____6249 in
                                                 (e, uu____6246, uu____6247) in
                                               FStar_Extraction_ML_Syntax.MLE_If
                                                 uu____6241 in
                                             FStar_All.pipe_left
                                               (FStar_Extraction_ML_Syntax.with_ty
                                                  t_branch) uu____6240 in
                                           let uu____6251 =
                                             FStar_Extraction_ML_Util.join
                                               then_e1.FStar_Syntax_Syntax.pos
                                               f_then f_else in
                                           (uu____6239, uu____6251, t_branch))))
                        | uu____6252 ->
                            failwith
                              "ITE pats matched but then and else expressions not found?")
                     else
                       (let uu____6261 =
                          FStar_All.pipe_right pats
                            (FStar_Util.fold_map
                               (fun compat  ->
                                  fun br  ->
                                    let uu____6310 =
                                      FStar_Syntax_Subst.open_branch br in
                                    match uu____6310 with
                                    | (pat,when_opt,branch1) ->
                                        let uu____6338 =
                                          extract_pat g pat t_e in
                                        (match uu____6338 with
                                         | (env,p,pat_t_compat) ->
                                             let uu____6369 =
                                               match when_opt with
                                               | None  ->
                                                   (None,
                                                     FStar_Extraction_ML_Syntax.E_PURE)
                                               | Some w ->
                                                   let uu____6384 =
                                                     term_as_mlexpr env w in
                                                   (match uu____6384 with
                                                    | (w1,f_w,t_w) ->
                                                        let w2 =
                                                          maybe_coerce env w1
                                                            t_w
                                                            FStar_Extraction_ML_Syntax.ml_bool_ty in
                                                        ((Some w2), f_w)) in
                                             (match uu____6369 with
                                              | (when_opt1,f_when) ->
                                                  let uu____6412 =
                                                    term_as_mlexpr env
                                                      branch1 in
                                                  (match uu____6412 with
                                                   | (mlbranch,f_branch,t_branch)
                                                       ->
                                                       let uu____6431 =
                                                         FStar_All.pipe_right
                                                           p
                                                           (FStar_List.map
                                                              (fun uu____6468
                                                                  ->
                                                                 match uu____6468
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
                                                         uu____6431))))) true) in
                        match uu____6261 with
                        | (pat_t_compat,mlbranches) ->
                            let mlbranches1 = FStar_List.flatten mlbranches in
                            let e1 =
                              if pat_t_compat
                              then e
                              else
                                (FStar_Extraction_ML_UEnv.debug g
                                   (fun uu____6554  ->
                                      let uu____6555 =
                                        FStar_Extraction_ML_Code.string_of_mlexpr
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          e in
                                      let uu____6556 =
                                        FStar_Extraction_ML_Code.string_of_mlty
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          t_e in
                                      FStar_Util.print2
                                        "Coercing scrutinee %s from type %s because pattern type is incompatible\n"
                                        uu____6555 uu____6556);
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty t_e)
                                   (FStar_Extraction_ML_Syntax.MLE_Coerce
                                      (e, t_e,
                                        FStar_Extraction_ML_Syntax.MLTY_Top))) in
                            (match mlbranches1 with
                             | [] ->
                                 let uu____6569 =
                                   let uu____6574 =
                                     let uu____6583 =
                                       FStar_Syntax_Syntax.lid_as_fv
                                         FStar_Syntax_Const.failwith_lid
                                         FStar_Syntax_Syntax.Delta_constant
                                         None in
                                     FStar_Extraction_ML_UEnv.lookup_fv g
                                       uu____6583 in
                                   FStar_All.pipe_left FStar_Util.right
                                     uu____6574 in
                                 (match uu____6569 with
                                  | (uu____6605,fw,uu____6607,uu____6608) ->
                                      let uu____6609 =
                                        let uu____6610 =
                                          let uu____6611 =
                                            let uu____6615 =
                                              let uu____6617 =
                                                FStar_All.pipe_left
                                                  (FStar_Extraction_ML_Syntax.with_ty
                                                     FStar_Extraction_ML_Syntax.ml_string_ty)
                                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                                     (FStar_Extraction_ML_Syntax.MLC_String
                                                        "unreachable")) in
                                              [uu____6617] in
                                            (fw, uu____6615) in
                                          FStar_Extraction_ML_Syntax.MLE_App
                                            uu____6611 in
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             FStar_Extraction_ML_Syntax.ml_unit_ty)
                                          uu____6610 in
                                      (uu____6609,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        FStar_Extraction_ML_Syntax.ml_unit_ty))
                             | (uu____6619,uu____6620,(uu____6621,f_first,t_first))::rest
                                 ->
                                 let uu____6653 =
                                   FStar_List.fold_left
                                     (fun uu____6669  ->
                                        fun uu____6670  ->
                                          match (uu____6669, uu____6670) with
                                          | ((topt,f),(uu____6700,uu____6701,
                                                       (uu____6702,f_branch,t_branch)))
                                              ->
                                              let f1 =
                                                FStar_Extraction_ML_Util.join
                                                  top.FStar_Syntax_Syntax.pos
                                                  f f_branch in
                                              let topt1 =
                                                match topt with
                                                | None  -> None
                                                | Some t1 ->
                                                    let uu____6733 =
                                                      type_leq g t1 t_branch in
                                                    if uu____6733
                                                    then Some t_branch
                                                    else
                                                      (let uu____6736 =
                                                         type_leq g t_branch
                                                           t1 in
                                                       if uu____6736
                                                       then Some t1
                                                       else None) in
                                              (topt1, f1))
                                     ((Some t_first), f_first) rest in
                                 (match uu____6653 with
                                  | (topt,f_match) ->
                                      let mlbranches2 =
                                        FStar_All.pipe_right mlbranches1
                                          (FStar_List.map
                                             (fun uu____6782  ->
                                                match uu____6782 with
                                                | (p,(wopt,uu____6798),
                                                   (b1,uu____6800,t1)) ->
                                                    let b2 =
                                                      match topt with
                                                      | None  ->
                                                          FStar_Extraction_ML_Syntax.apply_obj_repr
                                                            b1 t1
                                                      | Some uu____6811 -> b1 in
                                                    (p, wopt, b2))) in
                                      let t_match =
                                        match topt with
                                        | None  ->
                                            FStar_Extraction_ML_Syntax.MLTY_Top
                                        | Some t1 -> t1 in
                                      let uu____6815 =
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             t_match)
                                          (FStar_Extraction_ML_Syntax.MLE_Match
                                             (e1, mlbranches2)) in
                                      (uu____6815, f_match, t_match)))))))
let fresh: Prims.string -> (Prims.string* Prims.int) =
  let c = FStar_Util.mk_ref (Prims.parse_int "0") in
  fun x  ->
    FStar_Util.incr c; (let uu____6833 = FStar_ST.read c in (x, uu____6833))
let ind_discriminator_body:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlmodule1
  =
  fun env  ->
    fun discName  ->
      fun constrName  ->
        let uu____6845 =
          let uu____6848 =
            FStar_TypeChecker_Env.lookup_lid
              env.FStar_Extraction_ML_UEnv.tcenv discName in
          FStar_All.pipe_left FStar_Pervasives.fst uu____6848 in
        match uu____6845 with
        | (uu____6861,fstar_disc_type) ->
            let wildcards =
              let uu____6869 =
                let uu____6870 = FStar_Syntax_Subst.compress fstar_disc_type in
                uu____6870.FStar_Syntax_Syntax.n in
              match uu____6869 with
              | FStar_Syntax_Syntax.Tm_arrow (binders,uu____6879) ->
                  let uu____6890 =
                    FStar_All.pipe_right binders
                      (FStar_List.filter
                         (fun uu___140_6905  ->
                            match uu___140_6905 with
                            | (uu____6909,Some (FStar_Syntax_Syntax.Implicit
                               uu____6910)) -> true
                            | uu____6912 -> false)) in
                  FStar_All.pipe_right uu____6890
                    (FStar_List.map
                       (fun uu____6932  ->
                          let uu____6936 = fresh "_" in
                          (uu____6936, FStar_Extraction_ML_Syntax.MLTY_Top)))
              | uu____6941 -> failwith "Discriminator must be a function" in
            let mlid = fresh "_discr_" in
            let targ = FStar_Extraction_ML_Syntax.MLTY_Top in
            let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top in
            let discrBody =
              let uu____6953 =
                let uu____6954 =
                  let uu____6960 =
                    let uu____6961 =
                      let uu____6962 =
                        let uu____6970 =
                          let uu____6971 =
                            let uu____6972 =
                              let uu____6973 =
                                FStar_Extraction_ML_Syntax.idsym mlid in
                              ([], uu____6973) in
                            FStar_Extraction_ML_Syntax.MLE_Name uu____6972 in
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty targ)
                            uu____6971 in
                        let uu____6975 =
                          let uu____6981 =
                            let uu____6986 =
                              let uu____6987 =
                                let uu____6991 =
                                  FStar_Extraction_ML_Syntax.mlpath_of_lident
                                    constrName in
                                (uu____6991,
                                  [FStar_Extraction_ML_Syntax.MLP_Wild]) in
                              FStar_Extraction_ML_Syntax.MLP_CTor uu____6987 in
                            let uu____6993 =
                              FStar_All.pipe_left
                                (FStar_Extraction_ML_Syntax.with_ty
                                   FStar_Extraction_ML_Syntax.ml_bool_ty)
                                (FStar_Extraction_ML_Syntax.MLE_Const
                                   (FStar_Extraction_ML_Syntax.MLC_Bool true)) in
                            (uu____6986, None, uu____6993) in
                          let uu____6995 =
                            let uu____7001 =
                              let uu____7006 =
                                FStar_All.pipe_left
                                  (FStar_Extraction_ML_Syntax.with_ty
                                     FStar_Extraction_ML_Syntax.ml_bool_ty)
                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                     (FStar_Extraction_ML_Syntax.MLC_Bool
                                        false)) in
                              (FStar_Extraction_ML_Syntax.MLP_Wild, None,
                                uu____7006) in
                            [uu____7001] in
                          uu____6981 :: uu____6995 in
                        (uu____6970, uu____6975) in
                      FStar_Extraction_ML_Syntax.MLE_Match uu____6962 in
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.ml_bool_ty) uu____6961 in
                  ((FStar_List.append wildcards [(mlid, targ)]), uu____6960) in
                FStar_Extraction_ML_Syntax.MLE_Fun uu____6954 in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty disc_ty) uu____6953 in
            let uu____7044 =
              let uu____7045 =
                let uu____7047 =
                  let uu____7048 =
                    FStar_Extraction_ML_UEnv.convIdent
                      discName.FStar_Ident.ident in
                  {
                    FStar_Extraction_ML_Syntax.mllb_name = uu____7048;
                    FStar_Extraction_ML_Syntax.mllb_tysc = None;
                    FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                    FStar_Extraction_ML_Syntax.mllb_def = discrBody;
                    FStar_Extraction_ML_Syntax.print_typ = false
                  } in
                [uu____7047] in
              (FStar_Extraction_ML_Syntax.NonRec, [], uu____7045) in
            FStar_Extraction_ML_Syntax.MLM_Let uu____7044