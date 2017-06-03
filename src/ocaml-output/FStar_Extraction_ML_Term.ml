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
      | FStar_Syntax_Syntax.Tm_constant uu____336 -> false
      | FStar_Syntax_Syntax.Tm_name uu____337 -> false
      | FStar_Syntax_Syntax.Tm_bvar uu____338 -> false
      | FStar_Syntax_Syntax.Tm_type uu____339 -> true
      | FStar_Syntax_Syntax.Tm_arrow (uu____340,c) ->
          is_arity env (FStar_Syntax_Util.comp_result c)
      | FStar_Syntax_Syntax.Tm_fvar uu____352 ->
          let t2 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Normalize.AllowUnboundUniverses;
              FStar_TypeChecker_Normalize.EraseUniverses;
              FStar_TypeChecker_Normalize.UnfoldUntil
                FStar_Syntax_Syntax.Delta_constant]
              env.FStar_Extraction_ML_UEnv.tcenv t1 in
          let uu____354 =
            let uu____355 = FStar_Syntax_Subst.compress t2 in
            uu____355.FStar_Syntax_Syntax.n in
          (match uu____354 with
           | FStar_Syntax_Syntax.Tm_fvar uu____358 -> false
           | uu____359 -> is_arity env t2)
      | FStar_Syntax_Syntax.Tm_app uu____360 ->
          let uu____370 = FStar_Syntax_Util.head_and_args t1 in
          (match uu____370 with | (head1,uu____381) -> is_arity env head1)
      | FStar_Syntax_Syntax.Tm_uinst (head1,uu____397) -> is_arity env head1
      | FStar_Syntax_Syntax.Tm_refine (x,uu____403) ->
          is_arity env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_abs (uu____408,body,uu____410) ->
          is_arity env body
      | FStar_Syntax_Syntax.Tm_let (uu____433,body) -> is_arity env body
      | FStar_Syntax_Syntax.Tm_match (uu____445,branches) ->
          (match branches with
           | (uu____473,uu____474,e)::uu____476 -> is_arity env e
           | uu____512 -> false)
let rec is_type_aux:
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Subst.compress t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____531 ->
          let uu____552 =
            let uu____553 = FStar_Syntax_Print.tag_of_term t1 in
            FStar_Util.format1 "Impossible: %s" uu____553 in
          failwith uu____552
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____554 =
            let uu____555 = FStar_Syntax_Print.tag_of_term t1 in
            FStar_Util.format1 "Impossible: %s" uu____555 in
          failwith uu____554
      | FStar_Syntax_Syntax.Tm_constant uu____556 -> false
      | FStar_Syntax_Syntax.Tm_type uu____557 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____558 -> true
      | FStar_Syntax_Syntax.Tm_arrow uu____563 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.failwith_lid ->
          false
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____573 =
            FStar_TypeChecker_Env.is_type_constructor
              env.FStar_Extraction_ML_UEnv.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          if uu____573
          then true
          else
            (let uu____579 =
               FStar_TypeChecker_Env.lookup_lid
                 env.FStar_Extraction_ML_UEnv.tcenv
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
             match uu____579 with
             | ((uu____588,t2),uu____590) -> is_arity env t2)
      | FStar_Syntax_Syntax.Tm_uvar (uu____593,t2) -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_bvar
          { FStar_Syntax_Syntax.ppname = uu____607;
            FStar_Syntax_Syntax.index = uu____608;
            FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_name
          { FStar_Syntax_Syntax.ppname = uu____612;
            FStar_Syntax_Syntax.index = uu____613;
            FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____618,uu____619) ->
          is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____649) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_abs (uu____654,body,uu____656) ->
          is_type_aux env body
      | FStar_Syntax_Syntax.Tm_let (uu____679,body) -> is_type_aux env body
      | FStar_Syntax_Syntax.Tm_match (uu____691,branches) ->
          (match branches with
           | (uu____719,uu____720,e)::uu____722 -> is_type_aux env e
           | uu____758 -> false)
      | FStar_Syntax_Syntax.Tm_meta (t2,uu____771) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_app (head1,uu____777) -> is_type_aux env head1
let is_type:
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let b = is_type_aux env t in
      FStar_Extraction_ML_UEnv.debug env
        (fun uu____800  ->
           if b
           then
             let uu____801 = FStar_Syntax_Print.term_to_string t in
             let uu____802 = FStar_Syntax_Print.tag_of_term t in
             FStar_Util.print2 "is_type %s (%s)\n" uu____801 uu____802
           else
             (let uu____804 = FStar_Syntax_Print.term_to_string t in
              let uu____805 = FStar_Syntax_Print.tag_of_term t in
              FStar_Util.print2 "not a type %s (%s)\n" uu____804 uu____805));
      b
let is_type_binder env x = is_arity env (fst x).FStar_Syntax_Syntax.sort
let is_constructor: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____825 =
      let uu____826 = FStar_Syntax_Subst.compress t in
      uu____826.FStar_Syntax_Syntax.n in
    match uu____825 with
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____829;
          FStar_Syntax_Syntax.fv_delta = uu____830;
          FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor );_}
        -> true
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____834;
          FStar_Syntax_Syntax.fv_delta = uu____835;
          FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor
            uu____836);_}
        -> true
    | uu____843 -> false
let rec is_fstar_value: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____847 =
      let uu____848 = FStar_Syntax_Subst.compress t in
      uu____848.FStar_Syntax_Syntax.n in
    match uu____847 with
    | FStar_Syntax_Syntax.Tm_constant uu____851 -> true
    | FStar_Syntax_Syntax.Tm_bvar uu____852 -> true
    | FStar_Syntax_Syntax.Tm_fvar uu____853 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____854 -> true
    | FStar_Syntax_Syntax.Tm_app (head1,args) ->
        let uu____885 = is_constructor head1 in
        if uu____885
        then
          FStar_All.pipe_right args
            (FStar_List.for_all
               (fun uu____893  ->
                  match uu____893 with | (te,uu____897) -> is_fstar_value te))
        else false
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____900) -> is_fstar_value t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____906,uu____907) ->
        is_fstar_value t1
    | uu____936 -> false
let rec is_ml_value: FStar_Extraction_ML_Syntax.mlexpr -> Prims.bool =
  fun e  ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_Const uu____940 -> true
    | FStar_Extraction_ML_Syntax.MLE_Var uu____941 -> true
    | FStar_Extraction_ML_Syntax.MLE_Name uu____942 -> true
    | FStar_Extraction_ML_Syntax.MLE_Fun uu____943 -> true
    | FStar_Extraction_ML_Syntax.MLE_CTor (uu____949,exps) ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Tuple exps ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Record (uu____955,fields) ->
        FStar_Util.for_all
          (fun uu____967  ->
             match uu____967 with | (uu____970,e1) -> is_ml_value e1) fields
    | uu____972 -> false
let normalize_abs: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t0  ->
    let rec aux bs t copt =
      let t1 = FStar_Syntax_Subst.compress t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_abs (bs',body,copt1) ->
          aux (FStar_List.append bs bs') body copt1
      | uu____1032 ->
          let e' = FStar_Syntax_Util.unascribe t1 in
          let uu____1034 = FStar_Syntax_Util.is_fun e' in
          if uu____1034
          then aux bs e' copt
          else FStar_Syntax_Util.abs bs e' copt in
    aux [] t0 None
let unit_binder: FStar_Syntax_Syntax.binder =
  let uu____1043 =
    FStar_Syntax_Syntax.new_bv None FStar_TypeChecker_Common.t_unit in
  FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____1043
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
      (let uu____1089 = FStar_List.hd l in
       match uu____1089 with
       | (p1,w1,e1) ->
           let uu____1108 =
             let uu____1113 = FStar_List.tl l in FStar_List.hd uu____1113 in
           (match uu____1108 with
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
                 | uu____1152 -> def)))
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
            let uu____1195 = erasable g f ty in
            if uu____1195
            then
              let uu____1196 =
                type_leq g ty FStar_Extraction_ML_Syntax.ml_unit_ty in
              (if uu____1196
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
          let uu____1212 = type_leq_c g (Some e) ty1 expect in
          match uu____1212 with
          | (true ,Some e') -> e'
          | uu____1218 ->
              (FStar_Extraction_ML_UEnv.debug g
                 (fun uu____1223  ->
                    let uu____1224 =
                      FStar_Extraction_ML_Code.string_of_mlexpr
                        g.FStar_Extraction_ML_UEnv.currentModule e in
                    let uu____1225 =
                      FStar_Extraction_ML_Code.string_of_mlty
                        g.FStar_Extraction_ML_UEnv.currentModule ty1 in
                    let uu____1226 =
                      FStar_Extraction_ML_Code.string_of_mlty
                        g.FStar_Extraction_ML_UEnv.currentModule expect in
                    FStar_Util.print3
                      "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n"
                      uu____1224 uu____1225 uu____1226);
               FStar_All.pipe_left
                 (FStar_Extraction_ML_Syntax.with_ty expect)
                 (FStar_Extraction_ML_Syntax.MLE_Coerce (e, ty1, expect)))
let bv_as_mlty:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlty
  =
  fun g  ->
    fun bv  ->
      let uu____1233 = FStar_Extraction_ML_UEnv.lookup_bv g bv in
      match uu____1233 with
      | FStar_Util.Inl (uu____1234,t) -> t
      | uu____1242 -> FStar_Extraction_ML_Syntax.MLTY_Top
let rec term_as_mlty:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlty
  =
  fun g  ->
    fun t0  ->
      let rec is_top_ty t =
        match t with
        | FStar_Extraction_ML_Syntax.MLTY_Top  -> true
        | FStar_Extraction_ML_Syntax.MLTY_Named uu____1278 ->
            let uu____1282 = FStar_Extraction_ML_Util.udelta_unfold g t in
            (match uu____1282 with | None  -> false | Some t1 -> is_top_ty t1)
        | uu____1285 -> false in
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
      let uu____1288 = is_top_ty mlt in
      if uu____1288
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
      | FStar_Syntax_Syntax.Tm_bvar uu____1294 ->
          let uu____1295 =
            let uu____1296 = FStar_Syntax_Print.term_to_string t1 in
            FStar_Util.format1 "Impossible: Unexpected term %s" uu____1296 in
          failwith uu____1295
      | FStar_Syntax_Syntax.Tm_delayed uu____1297 ->
          let uu____1318 =
            let uu____1319 = FStar_Syntax_Print.term_to_string t1 in
            FStar_Util.format1 "Impossible: Unexpected term %s" uu____1319 in
          failwith uu____1318
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____1320 =
            let uu____1321 = FStar_Syntax_Print.term_to_string t1 in
            FStar_Util.format1 "Impossible: Unexpected term %s" uu____1321 in
          failwith uu____1320
      | FStar_Syntax_Syntax.Tm_constant uu____1322 ->
          FStar_Extraction_ML_UEnv.unknownType
      | FStar_Syntax_Syntax.Tm_uvar uu____1323 ->
          FStar_Extraction_ML_UEnv.unknownType
      | FStar_Syntax_Syntax.Tm_meta (t2,uu____1333) -> term_as_mlty' env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____1338;
             FStar_Syntax_Syntax.index = uu____1339;
             FStar_Syntax_Syntax.sort = t2;_},uu____1341)
          -> term_as_mlty' env t2
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____1349) -> term_as_mlty' env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____1355,uu____1356) ->
          term_as_mlty' env t2
      | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
      | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv []
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____1403 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____1403 with
           | (bs1,c1) ->
               let uu____1408 = binders_as_ml_binders env bs1 in
               (match uu____1408 with
                | (mlbs,env1) ->
                    let t_ret =
                      let eff =
                        FStar_TypeChecker_Env.norm_eff_name
                          env1.FStar_Extraction_ML_UEnv.tcenv
                          (FStar_Syntax_Util.comp_effect_name c1) in
                      let uu____1424 =
                        let uu____1428 =
                          FStar_TypeChecker_Env.effect_decl_opt
                            env1.FStar_Extraction_ML_UEnv.tcenv eff in
                        FStar_Util.must uu____1428 in
                      match uu____1424 with
                      | (ed,qualifiers) ->
                          let uu____1440 =
                            FStar_All.pipe_right qualifiers
                              (FStar_List.contains
                                 FStar_Syntax_Syntax.Reifiable) in
                          if uu____1440
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
                    let uu____1446 =
                      FStar_List.fold_right
                        (fun uu____1453  ->
                           fun uu____1454  ->
                             match (uu____1453, uu____1454) with
                             | ((uu____1465,t2),(tag,t')) ->
                                 (FStar_Extraction_ML_Syntax.E_PURE,
                                   (FStar_Extraction_ML_Syntax.MLTY_Fun
                                      (t2, tag, t')))) mlbs (erase1, t_ret) in
                    (match uu____1446 with | (uu____1473,t2) -> t2)))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let res =
            let uu____1492 =
              let uu____1493 = FStar_Syntax_Util.un_uinst head1 in
              uu____1493.FStar_Syntax_Syntax.n in
            match uu____1492 with
            | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
            | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv args
            | FStar_Syntax_Syntax.Tm_app (head2,args') ->
                let uu____1514 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app
                       (head2, (FStar_List.append args' args))) None
                    t1.FStar_Syntax_Syntax.pos in
                term_as_mlty' env uu____1514
            | uu____1530 -> FStar_Extraction_ML_UEnv.unknownType in
          res
      | FStar_Syntax_Syntax.Tm_abs (bs,ty,uu____1533) ->
          let uu____1556 = FStar_Syntax_Subst.open_term bs ty in
          (match uu____1556 with
           | (bs1,ty1) ->
               let uu____1561 = binders_as_ml_binders env bs1 in
               (match uu____1561 with | (bts,env1) -> term_as_mlty' env1 ty1))
      | FStar_Syntax_Syntax.Tm_type uu____1575 ->
          FStar_Extraction_ML_UEnv.unknownType
      | FStar_Syntax_Syntax.Tm_let uu____1576 ->
          FStar_Extraction_ML_UEnv.unknownType
      | FStar_Syntax_Syntax.Tm_match uu____1584 ->
          FStar_Extraction_ML_UEnv.unknownType
and arg_as_mlty:
  FStar_Extraction_ML_UEnv.env ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.aqual) ->
      FStar_Extraction_ML_Syntax.mlty
  =
  fun g  ->
    fun uu____1601  ->
      match uu____1601 with
      | (a,uu____1605) ->
          let uu____1606 = is_type g a in
          if uu____1606
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
        let uu____1611 =
          FStar_Syntax_Util.arrow_formals
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.ty in
        match uu____1611 with
        | (formals,t) ->
            let mlargs = FStar_List.map (arg_as_mlty g) args in
            let mlargs1 =
              let n_args = FStar_List.length args in
              if (FStar_List.length formals) > n_args
              then
                let uu____1661 = FStar_Util.first_N n_args formals in
                match uu____1661 with
                | (uu____1677,rest) ->
                    let uu____1691 =
                      FStar_List.map
                        (fun uu____1695  ->
                           FStar_Extraction_ML_UEnv.erasedContent) rest in
                    FStar_List.append mlargs uu____1691
              else mlargs in
            let nm =
              let uu____1700 =
                FStar_Extraction_ML_UEnv.maybe_mangle_type_projector g fv in
              match uu____1700 with
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
      let uu____1715 =
        FStar_All.pipe_right bs
          (FStar_List.fold_left
             (fun uu____1739  ->
                fun b  ->
                  match uu____1739 with
                  | (ml_bs,env) ->
                      let uu____1769 = is_type_binder g b in
                      if uu____1769
                      then
                        let b1 = fst b in
                        let env1 =
                          FStar_Extraction_ML_UEnv.extend_ty env b1
                            (Some FStar_Extraction_ML_Syntax.MLTY_Top) in
                        let ml_b =
                          let uu____1784 =
                            FStar_Extraction_ML_UEnv.bv_as_ml_termvar b1 in
                          (uu____1784, FStar_Extraction_ML_Syntax.ml_unit_ty) in
                        ((ml_b :: ml_bs), env1)
                      else
                        (let b1 = fst b in
                         let t = term_as_mlty env b1.FStar_Syntax_Syntax.sort in
                         let uu____1801 =
                           FStar_Extraction_ML_UEnv.extend_bv env b1 
                             ([], t) false false false in
                         match uu____1801 with
                         | (env1,b2) ->
                             let ml_b =
                               let uu____1819 =
                                 FStar_Extraction_ML_UEnv.removeTick b2 in
                               (uu____1819, t) in
                             ((ml_b :: ml_bs), env1))) ([], g)) in
      match uu____1715 with | (ml_bs,env) -> ((FStar_List.rev ml_bs), env)
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
      | (FStar_Extraction_ML_Syntax.MLE_Seq es1,uu____1879) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (FStar_List.append es1 [e2])
      | (uu____1881,FStar_Extraction_ML_Syntax.MLE_Seq es2) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (e1 :: es2)
      | uu____1884 -> FStar_Extraction_ML_Syntax.MLE_Seq [e1; e2]
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
                    | uu____1906 when
                        (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
                          =
                          FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr
                        -> body.FStar_Extraction_ML_Syntax.expr
                    | uu____1907 ->
                        mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def
                          body)
             | uu____1908 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body))
        | uu____1910 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body)
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
           | uu____1924 ->
               (match q with
                | Some (FStar_Syntax_Syntax.Record_ctor (ty,fns)) ->
                    let path =
                      FStar_List.map FStar_Ident.text_of_id ty.FStar_Ident.ns in
                    let fs = record_fields fns pats in
                    FStar_Extraction_ML_Syntax.MLP_Record (path, fs)
                | uu____1940 -> p))
      | uu____1942 -> p
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
                     (fun uu____1978  ->
                        let uu____1979 =
                          FStar_Extraction_ML_Code.string_of_mlty
                            g.FStar_Extraction_ML_UEnv.currentModule t' in
                        let uu____1980 =
                          FStar_Extraction_ML_Code.string_of_mlty
                            g.FStar_Extraction_ML_UEnv.currentModule t in
                        FStar_Util.print2
                          "Expected pattern type %s; got pattern type %s\n"
                          uu____1979 uu____1980)
                 else ();
                 ok) in
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int
              (c,None )) ->
              let i = FStar_Const.Const_int (c, None) in
              let x = FStar_Extraction_ML_Syntax.gensym () in
              let when_clause =
                let uu____2003 =
                  let uu____2004 =
                    let uu____2008 =
                      let uu____2010 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.ml_int_ty)
                          (FStar_Extraction_ML_Syntax.MLE_Var x) in
                      let uu____2011 =
                        let uu____2013 =
                          let uu____2014 =
                            let uu____2015 =
                              FStar_Extraction_ML_Util.mlconst_of_const'
                                p.FStar_Syntax_Syntax.p i in
                            FStar_All.pipe_left
                              (fun _0_31  ->
                                 FStar_Extraction_ML_Syntax.MLE_Const _0_31)
                              uu____2015 in
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty
                               FStar_Extraction_ML_Syntax.ml_int_ty)
                            uu____2014 in
                        [uu____2013] in
                      uu____2010 :: uu____2011 in
                    (FStar_Extraction_ML_Util.prims_op_equality, uu____2008) in
                  FStar_Extraction_ML_Syntax.MLE_App uu____2004 in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     FStar_Extraction_ML_Syntax.ml_bool_ty) uu____2003 in
              let uu____2017 = ok FStar_Extraction_ML_Syntax.ml_int_ty in
              (g,
                (Some ((FStar_Extraction_ML_Syntax.MLP_Var x), [when_clause])),
                uu____2017)
          | FStar_Syntax_Syntax.Pat_constant s ->
              let t =
                FStar_TypeChecker_TcTerm.tc_constant FStar_Range.dummyRange s in
              let mlty = term_as_mlty g t in
              let uu____2029 =
                let uu____2034 =
                  let uu____2038 =
                    let uu____2039 =
                      FStar_Extraction_ML_Util.mlconst_of_const'
                        p.FStar_Syntax_Syntax.p s in
                    FStar_Extraction_ML_Syntax.MLP_Const uu____2039 in
                  (uu____2038, []) in
                Some uu____2034 in
              let uu____2044 = ok mlty in (g, uu____2029, uu____2044)
          | FStar_Syntax_Syntax.Pat_var x ->
              let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort in
              let uu____2051 =
                FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false false
                  imp in
              (match uu____2051 with
               | (g1,x1) ->
                   let uu____2064 = ok mlty in
                   (g1,
                     (if imp
                      then None
                      else Some ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                     uu____2064))
          | FStar_Syntax_Syntax.Pat_wild x ->
              let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort in
              let uu____2083 =
                FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false false
                  imp in
              (match uu____2083 with
               | (g1,x1) ->
                   let uu____2096 = ok mlty in
                   (g1,
                     (if imp
                      then None
                      else Some ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                     uu____2096))
          | FStar_Syntax_Syntax.Pat_dot_term uu____2113 -> (g, None, true)
          | FStar_Syntax_Syntax.Pat_cons (f,pats) ->
              let uu____2137 =
                let uu____2140 = FStar_Extraction_ML_UEnv.lookup_fv g f in
                match uu____2140 with
                | FStar_Util.Inr
                    (uu____2143,{
                                  FStar_Extraction_ML_Syntax.expr =
                                    FStar_Extraction_ML_Syntax.MLE_Name n1;
                                  FStar_Extraction_ML_Syntax.mlty =
                                    uu____2145;
                                  FStar_Extraction_ML_Syntax.loc = uu____2146;_},ttys,uu____2148)
                    -> (n1, ttys)
                | uu____2155 -> failwith "Expected a constructor" in
              (match uu____2137 with
               | (d,tys) ->
                   let nTyVars = FStar_List.length (fst tys) in
                   let uu____2170 = FStar_Util.first_N nTyVars pats in
                   (match uu____2170 with
                    | (tysVarPats,restPats) ->
                        let f_ty_opt =
                          try
                            let mlty_args =
                              FStar_All.pipe_right tysVarPats
                                (FStar_List.map
                                   (fun uu____2246  ->
                                      match uu____2246 with
                                      | (p1,uu____2252) ->
                                          (match p1.FStar_Syntax_Syntax.v
                                           with
                                           | FStar_Syntax_Syntax.Pat_dot_term
                                               (uu____2257,t) ->
                                               term_as_mlty g t
                                           | uu____2263 ->
                                               (FStar_Extraction_ML_UEnv.debug
                                                  g
                                                  (fun uu____2265  ->
                                                     let uu____2266 =
                                                       FStar_Syntax_Print.pat_to_string
                                                         p1 in
                                                     FStar_Util.print1
                                                       "Pattern %s is not extractable"
                                                       uu____2266);
                                                raise Un_extractable)))) in
                            let f_ty =
                              FStar_Extraction_ML_Util.subst tys mlty_args in
                            let uu____2268 =
                              FStar_Extraction_ML_Util.uncurry_mlty_fun f_ty in
                            Some uu____2268
                          with | Un_extractable  -> None in
                        let uu____2283 =
                          FStar_Util.fold_map
                            (fun g1  ->
                               fun uu____2298  ->
                                 match uu____2298 with
                                 | (p1,imp1) ->
                                     let uu____2309 =
                                       extract_one_pat true g1 p1 None in
                                     (match uu____2309 with
                                      | (g2,p2,uu____2325) -> (g2, p2))) g
                            tysVarPats in
                        (match uu____2283 with
                         | (g1,tyMLPats) ->
                             let uu____2357 =
                               FStar_Util.fold_map
                                 (fun uu____2383  ->
                                    fun uu____2384  ->
                                      match (uu____2383, uu____2384) with
                                      | ((g2,f_ty_opt1),(p1,imp1)) ->
                                          let uu____2433 =
                                            match f_ty_opt1 with
                                            | Some (hd1::rest,res) ->
                                                ((Some (rest, res)),
                                                  (Some hd1))
                                            | uu____2465 -> (None, None) in
                                          (match uu____2433 with
                                           | (f_ty_opt2,expected_ty) ->
                                               let uu____2502 =
                                                 extract_one_pat false g2 p1
                                                   expected_ty in
                                               (match uu____2502 with
                                                | (g3,p2,uu____2524) ->
                                                    ((g3, f_ty_opt2), p2))))
                                 (g1, f_ty_opt) restPats in
                             (match uu____2357 with
                              | ((g2,f_ty_opt1),restMLPats) ->
                                  let uu____2585 =
                                    let uu____2591 =
                                      FStar_All.pipe_right
                                        (FStar_List.append tyMLPats
                                           restMLPats)
                                        (FStar_List.collect
                                           (fun uu___138_2616  ->
                                              match uu___138_2616 with
                                              | Some x -> [x]
                                              | uu____2638 -> [])) in
                                    FStar_All.pipe_right uu____2591
                                      FStar_List.split in
                                  (match uu____2585 with
                                   | (mlPats,when_clauses) ->
                                       let pat_ty_compat =
                                         match f_ty_opt1 with
                                         | Some ([],t) -> ok t
                                         | uu____2677 -> false in
                                       let uu____2682 =
                                         let uu____2687 =
                                           let uu____2691 =
                                             resugar_pat
                                               f.FStar_Syntax_Syntax.fv_qual
                                               (FStar_Extraction_ML_Syntax.MLP_CTor
                                                  (d, mlPats)) in
                                           let uu____2693 =
                                             FStar_All.pipe_right
                                               when_clauses
                                               FStar_List.flatten in
                                           (uu____2691, uu____2693) in
                                         Some uu____2687 in
                                       (g2, uu____2682, pat_ty_compat))))))
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
          let uu____2747 = extract_one_pat false g1 p1 expected_t1 in
          match uu____2747 with
          | (g2,Some (x,v1),b) -> (g2, (x, v1), b)
          | uu____2778 -> failwith "Impossible: Unable to translate pattern" in
        let mk_when_clause whens =
          match whens with
          | [] -> None
          | hd1::tl1 ->
              let uu____2803 =
                FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd1 tl1 in
              Some uu____2803 in
        let uu____2804 = extract_one_pat1 g p (Some expected_t) in
        match uu____2804 with
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
            | FStar_Extraction_ML_Syntax.MLTY_Fun (t0,uu____2886,t1) ->
                let x = FStar_Extraction_ML_Syntax.gensym () in
                let uu____2889 =
                  let uu____2895 =
                    let uu____2900 =
                      FStar_All.pipe_left
                        (FStar_Extraction_ML_Syntax.with_ty t0)
                        (FStar_Extraction_ML_Syntax.MLE_Var x) in
                    ((x, t0), uu____2900) in
                  uu____2895 :: more_args in
                eta_args uu____2889 t1
            | FStar_Extraction_ML_Syntax.MLTY_Named (uu____2907,uu____2908)
                -> ((FStar_List.rev more_args), t)
            | uu____2920 -> failwith "Impossible: Head type is not an arrow" in
          let as_record qual1 e =
            match ((e.FStar_Extraction_ML_Syntax.expr), qual1) with
            | (FStar_Extraction_ML_Syntax.MLE_CTor (uu____2938,args),Some
               (FStar_Syntax_Syntax.Record_ctor (tyname,fields))) ->
                let path =
                  FStar_List.map FStar_Ident.text_of_id tyname.FStar_Ident.ns in
                let fields1 = record_fields fields args in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     e.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_Record (path, fields1))
            | uu____2957 -> e in
          let resugar_and_maybe_eta qual1 e =
            let uu____2970 = eta_args [] residualType in
            match uu____2970 with
            | (eargs,tres) ->
                (match eargs with
                 | [] ->
                     let uu____2998 = as_record qual1 e in
                     FStar_Extraction_ML_Util.resugar_exp uu____2998
                 | uu____2999 ->
                     let uu____3005 = FStar_List.unzip eargs in
                     (match uu____3005 with
                      | (binders,eargs1) ->
                          (match e.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_CTor (head1,args)
                               ->
                               let body =
                                 let uu____3029 =
                                   let uu____3030 =
                                     FStar_All.pipe_left
                                       (FStar_Extraction_ML_Syntax.with_ty
                                          tres)
                                       (FStar_Extraction_ML_Syntax.MLE_CTor
                                          (head1,
                                            (FStar_List.append args eargs1))) in
                                   FStar_All.pipe_left (as_record qual1)
                                     uu____3030 in
                                 FStar_All.pipe_left
                                   FStar_Extraction_ML_Util.resugar_exp
                                   uu____3029 in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    e.FStar_Extraction_ML_Syntax.mlty)
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    (binders, body))
                           | uu____3035 ->
                               failwith "Impossible: Not a constructor"))) in
          match ((mlAppExpr.FStar_Extraction_ML_Syntax.expr), qual) with
          | (uu____3037,None ) -> mlAppExpr
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____3040;
                FStar_Extraction_ML_Syntax.loc = uu____3041;_},mle::args),Some
             (FStar_Syntax_Syntax.Record_projector (constrname,f))) ->
              let f1 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append constrname.FStar_Ident.ns [f]) in
              let fn = FStar_Extraction_ML_Util.mlpath_of_lid f1 in
              let proj = FStar_Extraction_ML_Syntax.MLE_Proj (mle, fn) in
              let e =
                match args with
                | [] -> proj
                | uu____3059 ->
                    let uu____3061 =
                      let uu____3065 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj in
                      (uu____3065, args) in
                    FStar_Extraction_ML_Syntax.MLE_App uu____3061 in
              FStar_Extraction_ML_Syntax.with_ty
                mlAppExpr.FStar_Extraction_ML_Syntax.mlty e
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____3068;
                FStar_Extraction_ML_Syntax.loc = uu____3069;_},mlargs),Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____3074 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs)) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____3074
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____3077;
                FStar_Extraction_ML_Syntax.loc = uu____3078;_},mlargs),Some
             (FStar_Syntax_Syntax.Record_ctor uu____3080)) ->
              let uu____3087 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs)) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____3087
          | (FStar_Extraction_ML_Syntax.MLE_Name mlp,Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____3091 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, [])) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____3091
          | (FStar_Extraction_ML_Syntax.MLE_Name mlp,Some
             (FStar_Syntax_Syntax.Record_ctor uu____3094)) ->
              let uu____3099 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, [])) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____3099
          | uu____3101 -> mlAppExpr
let maybe_downgrade_eff:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.e_tag ->
      FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.e_tag
  =
  fun g  ->
    fun f  ->
      fun t  ->
        let uu____3114 =
          (f = FStar_Extraction_ML_Syntax.E_GHOST) &&
            (type_leq g t FStar_Extraction_ML_Syntax.ml_unit_ty) in
        if uu____3114 then FStar_Extraction_ML_Syntax.E_PURE else f
let rec term_as_mlexpr:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Extraction_ML_Syntax.mlexpr* FStar_Extraction_ML_Syntax.e_tag*
        FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun t  ->
      let uu____3155 = term_as_mlexpr' g t in
      match uu____3155 with
      | (e,tag,ty) ->
          let tag1 = maybe_downgrade_eff g tag ty in
          (FStar_Extraction_ML_UEnv.debug g
             (fun u  ->
                let uu____3168 =
                  let uu____3169 = FStar_Syntax_Print.tag_of_term t in
                  let uu____3170 = FStar_Syntax_Print.term_to_string t in
                  let uu____3171 =
                    FStar_Extraction_ML_Code.string_of_mlty
                      g.FStar_Extraction_ML_UEnv.currentModule ty in
                  FStar_Util.format4
                    "term_as_mlexpr (%s) :  %s has ML type %s and effect %s\n"
                    uu____3169 uu____3170 uu____3171
                    (FStar_Extraction_ML_Util.eff_to_string tag1) in
                FStar_Util.print_string uu____3168);
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
          let uu____3178 = check_term_as_mlexpr' g t f ty in
          match uu____3178 with
          | (e,t1) ->
              let uu____3185 = erase g e t1 f in
              (match uu____3185 with | (r,uu____3192,t2) -> (r, t2))
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
          let uu____3200 = term_as_mlexpr g e0 in
          match uu____3200 with
          | (e,tag,t) ->
              let tag1 = maybe_downgrade_eff g tag t in
              if FStar_Extraction_ML_Util.eff_leq tag1 f
              then let uu____3212 = maybe_coerce g e t ty in (uu____3212, ty)
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
           let uu____3223 =
             let uu____3224 =
               FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos in
             let uu____3225 = FStar_Syntax_Print.tag_of_term top in
             let uu____3226 = FStar_Syntax_Print.term_to_string top in
             FStar_Util.format3 "%s: term_as_mlexpr' (%s) :  %s \n"
               uu____3224 uu____3225 uu____3226 in
           FStar_Util.print_string uu____3223);
      (let t = FStar_Syntax_Subst.compress top in
       match t.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____3231 =
             let uu____3232 = FStar_Syntax_Print.tag_of_term t in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____3232 in
           failwith uu____3231
       | FStar_Syntax_Syntax.Tm_delayed uu____3236 ->
           let uu____3257 =
             let uu____3258 = FStar_Syntax_Print.tag_of_term t in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____3258 in
           failwith uu____3257
       | FStar_Syntax_Syntax.Tm_uvar uu____3262 ->
           let uu____3271 =
             let uu____3272 = FStar_Syntax_Print.tag_of_term t in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____3272 in
           failwith uu____3271
       | FStar_Syntax_Syntax.Tm_bvar uu____3276 ->
           let uu____3277 =
             let uu____3278 = FStar_Syntax_Print.tag_of_term t in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____3278 in
           failwith uu____3277
       | FStar_Syntax_Syntax.Tm_type uu____3282 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_refine uu____3283 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_arrow uu____3288 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Mutable_alloc ))
           ->
           let uu____3301 = term_as_mlexpr' g t1 in
           (match uu____3301 with
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
            | uu____3328 -> failwith "impossible")
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_monadic (m,uu____3337)) ->
           let t2 = FStar_Syntax_Subst.compress t1 in
           (match t2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) when
                FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname ->
                let uu____3360 =
                  let uu____3364 =
                    FStar_TypeChecker_Env.effect_decl_opt
                      g.FStar_Extraction_ML_UEnv.tcenv m in
                  FStar_Util.must uu____3364 in
                (match uu____3360 with
                 | (ed,qualifiers) ->
                     let uu____3379 =
                       let uu____3380 =
                         FStar_All.pipe_right qualifiers
                           (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
                       FStar_All.pipe_right uu____3380 Prims.op_Negation in
                     if uu____3379
                     then term_as_mlexpr' g t2
                     else
                       failwith
                         "This should not happen (should have been handled at Tm_abs level)")
            | uu____3389 -> term_as_mlexpr' g t2)
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____3391) -> term_as_mlexpr' g t1
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____3397) -> term_as_mlexpr' g t1
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____3403 =
             FStar_TypeChecker_TcTerm.type_of_tot_term
               g.FStar_Extraction_ML_UEnv.tcenv t in
           (match uu____3403 with
            | (uu____3410,ty,uu____3412) ->
                let ml_ty = term_as_mlty g ty in
                let uu____3414 =
                  let uu____3415 =
                    let uu____3416 =
                      FStar_Extraction_ML_Util.mlconst_of_const'
                        t.FStar_Syntax_Syntax.pos c in
                    FStar_All.pipe_left
                      (fun _0_32  ->
                         FStar_Extraction_ML_Syntax.MLE_Const _0_32)
                      uu____3416 in
                  FStar_Extraction_ML_Syntax.with_ty ml_ty uu____3415 in
                (uu____3414, FStar_Extraction_ML_Syntax.E_PURE, ml_ty))
       | FStar_Syntax_Syntax.Tm_name uu____3417 ->
           let uu____3418 = is_type g t in
           if uu____3418
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____3423 = FStar_Extraction_ML_UEnv.lookup_term g t in
              match uu____3423 with
              | (FStar_Util.Inl uu____3430,uu____3431) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | (FStar_Util.Inr (uu____3450,x,mltys,uu____3453),qual) ->
                  (match mltys with
                   | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                       ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | ([],t1) ->
                       let uu____3478 =
                         maybe_eta_data_and_project_record g qual t1 x in
                       (uu____3478, FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | uu____3479 -> err_uninst g t mltys t))
       | FStar_Syntax_Syntax.Tm_fvar uu____3483 ->
           let uu____3484 = is_type g t in
           if uu____3484
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____3489 = FStar_Extraction_ML_UEnv.lookup_term g t in
              match uu____3489 with
              | (FStar_Util.Inl uu____3496,uu____3497) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | (FStar_Util.Inr (uu____3516,x,mltys,uu____3519),qual) ->
                  (match mltys with
                   | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                       ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | ([],t1) ->
                       let uu____3544 =
                         maybe_eta_data_and_project_record g qual t1 x in
                       (uu____3544, FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | uu____3545 -> err_uninst g t mltys t))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,copt) ->
           let uu____3574 = FStar_Syntax_Subst.open_term bs body in
           (match uu____3574 with
            | (bs1,body1) ->
                let uu____3582 = binders_as_ml_binders g bs1 in
                (match uu____3582 with
                 | (ml_bs,env) ->
                     let body2 =
                       match copt with
                       | Some c ->
                           (FStar_Extraction_ML_UEnv.debug g
                              (fun uu____3612  ->
                                 match c with
                                 | FStar_Util.Inl lc ->
                                     let uu____3617 =
                                       FStar_Syntax_Print.lcomp_to_string lc in
                                     FStar_Util.print1 "Computation lc: %s\n"
                                       uu____3617
                                 | FStar_Util.Inr rc ->
                                     FStar_Util.print1 "Computation rc: %s\n"
                                       (FStar_Ident.text_of_lid (fst rc)));
                            (let uu____3626 =
                               FStar_TypeChecker_Env.is_reifiable
                                 env.FStar_Extraction_ML_UEnv.tcenv c in
                             if uu____3626
                             then
                               FStar_TypeChecker_Util.reify_body
                                 env.FStar_Extraction_ML_UEnv.tcenv body1
                             else body1))
                       | None  ->
                           (FStar_Extraction_ML_UEnv.debug g
                              (fun uu____3634  ->
                                 let uu____3635 =
                                   FStar_Syntax_Print.term_to_string body1 in
                                 FStar_Util.print1
                                   "No computation type for: %s\n" uu____3635);
                            body1) in
                     let uu____3636 = term_as_mlexpr env body2 in
                     (match uu____3636 with
                      | (ml_body,f,t1) ->
                          let uu____3646 =
                            FStar_List.fold_right
                              (fun uu____3653  ->
                                 fun uu____3654  ->
                                   match (uu____3653, uu____3654) with
                                   | ((uu____3665,targ),(f1,t2)) ->
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         (FStar_Extraction_ML_Syntax.MLTY_Fun
                                            (targ, f1, t2)))) ml_bs (f, t1) in
                          (match uu____3646 with
                           | (f1,tfun) ->
                               let uu____3678 =
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty tfun)
                                   (FStar_Extraction_ML_Syntax.MLE_Fun
                                      (ml_bs, ml_body)) in
                               (uu____3678, f1, tfun)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____3682);
              FStar_Syntax_Syntax.tk = uu____3683;
              FStar_Syntax_Syntax.pos = uu____3684;
              FStar_Syntax_Syntax.vars = uu____3685;_},uu____3686)
           -> failwith "Unreachable? Tm_app Const_reflect"
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let is_total uu___140_3728 =
             match uu___140_3728 with
             | FStar_Util.Inl l -> FStar_Syntax_Util.is_total_lcomp l
             | FStar_Util.Inr (l,flags) ->
                 (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid)
                   ||
                   (FStar_All.pipe_right flags
                      (FStar_List.existsb
                         (fun uu___139_3746  ->
                            match uu___139_3746 with
                            | FStar_Syntax_Syntax.TOTAL  -> true
                            | uu____3747 -> false))) in
           let uu____3748 =
             let uu____3751 =
               let uu____3752 = FStar_Syntax_Subst.compress head1 in
               uu____3752.FStar_Syntax_Syntax.n in
             ((head1.FStar_Syntax_Syntax.n), uu____3751) in
           (match uu____3748 with
            | (FStar_Syntax_Syntax.Tm_uvar uu____3758,uu____3759) ->
                let t1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.Iota;
                    FStar_TypeChecker_Normalize.Zeta;
                    FStar_TypeChecker_Normalize.EraseUniverses;
                    FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                    g.FStar_Extraction_ML_UEnv.tcenv t in
                term_as_mlexpr' g t1
            | (uu____3769,FStar_Syntax_Syntax.Tm_abs (bs,uu____3771,Some lc))
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
            | (uu____3800,FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_reify )) ->
                let e =
                  let uu____3802 = FStar_List.hd args in
                  FStar_TypeChecker_Util.reify_body_with_arg
                    g.FStar_Extraction_ML_UEnv.tcenv head1 uu____3802 in
                let tm =
                  let uu____3810 =
                    let uu____3811 = FStar_TypeChecker_Util.remove_reify e in
                    let uu____3812 = FStar_List.tl args in
                    FStar_Syntax_Syntax.mk_Tm_app uu____3811 uu____3812 in
                  uu____3810 None t.FStar_Syntax_Syntax.pos in
                term_as_mlexpr' g tm
            | uu____3821 ->
                let rec extract_app is_data uu____3849 uu____3850 restArgs =
                  match (uu____3849, uu____3850) with
                  | ((mlhead,mlargs_f),(f,t1)) ->
                      (match (restArgs, t1) with
                       | ([],uu____3898) ->
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
                                | uu____3914 -> false) in
                           let uu____3915 =
                             if evaluation_order_guaranteed
                             then
                               let uu____3928 =
                                 FStar_All.pipe_right
                                   (FStar_List.rev mlargs_f)
                                   (FStar_List.map FStar_Pervasives.fst) in
                               ([], uu____3928)
                             else
                               FStar_List.fold_left
                                 (fun uu____3953  ->
                                    fun uu____3954  ->
                                      match (uu____3953, uu____3954) with
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
                                             let uu____4009 =
                                               let uu____4011 =
                                                 FStar_All.pipe_left
                                                   (FStar_Extraction_ML_Syntax.with_ty
                                                      arg.FStar_Extraction_ML_Syntax.mlty)
                                                   (FStar_Extraction_ML_Syntax.MLE_Var
                                                      x) in
                                               uu____4011 :: out_args in
                                             (((x, arg) :: lbs), uu____4009)))
                                 ([], []) mlargs_f in
                           (match uu____3915 with
                            | (lbs,mlargs) ->
                                let app =
                                  let uu____4038 =
                                    FStar_All.pipe_left
                                      (FStar_Extraction_ML_Syntax.with_ty t1)
                                      (FStar_Extraction_ML_Syntax.MLE_App
                                         (mlhead, mlargs)) in
                                  FStar_All.pipe_left
                                    (maybe_eta_data_and_project_record g
                                       is_data t1) uu____4038 in
                                let l_app =
                                  FStar_List.fold_right
                                    (fun uu____4043  ->
                                       fun out  ->
                                         match uu____4043 with
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
                       | ((arg,uu____4056)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                          (formal_t,f',t2)) when
                           (is_type g arg) &&
                             (type_leq g formal_t
                                FStar_Extraction_ML_Syntax.ml_unit_ty)
                           ->
                           let uu____4074 =
                             let uu____4077 =
                               FStar_Extraction_ML_Util.join
                                 arg.FStar_Syntax_Syntax.pos f f' in
                             (uu____4077, t2) in
                           extract_app is_data
                             (mlhead,
                               ((FStar_Extraction_ML_Syntax.ml_unit,
                                  FStar_Extraction_ML_Syntax.E_PURE) ::
                               mlargs_f)) uu____4074 rest
                       | ((e0,uu____4084)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                          (tExpected,f',t2)) ->
                           let r = e0.FStar_Syntax_Syntax.pos in
                           let uu____4103 = term_as_mlexpr g e0 in
                           (match uu____4103 with
                            | (e01,f0,tInferred) ->
                                let e02 =
                                  maybe_coerce g e01 tInferred tExpected in
                                let uu____4114 =
                                  let uu____4117 =
                                    FStar_Extraction_ML_Util.join_l r
                                      [f; f'; f0] in
                                  (uu____4117, t2) in
                                extract_app is_data
                                  (mlhead, ((e02, f0) :: mlargs_f))
                                  uu____4114 rest)
                       | uu____4123 ->
                           let uu____4130 =
                             FStar_Extraction_ML_Util.udelta_unfold g t1 in
                           (match uu____4130 with
                            | Some t2 ->
                                extract_app is_data (mlhead, mlargs_f)
                                  (f, t2) restArgs
                            | None  ->
                                err_ill_typed_application g top restArgs t1)) in
                let extract_app_maybe_projector is_data mlhead uu____4166
                  args1 =
                  match uu____4166 with
                  | (f,t1) ->
                      (match is_data with
                       | Some (FStar_Syntax_Syntax.Record_projector
                           uu____4185) ->
                           let rec remove_implicits args2 f1 t2 =
                             match (args2, t2) with
                             | ((a0,Some (FStar_Syntax_Syntax.Implicit
                                 uu____4235))::args3,FStar_Extraction_ML_Syntax.MLTY_Fun
                                (uu____4237,f',t3)) ->
                                 let uu____4262 =
                                   FStar_Extraction_ML_Util.join
                                     a0.FStar_Syntax_Syntax.pos f1 f' in
                                 remove_implicits args3 uu____4262 t3
                             | uu____4263 -> (args2, f1, t2) in
                           let uu____4278 = remove_implicits args1 f t1 in
                           (match uu____4278 with
                            | (args2,f1,t2) ->
                                extract_app is_data (mlhead, []) (f1, t2)
                                  args2)
                       | uu____4311 ->
                           extract_app is_data (mlhead, []) (f, t1) args1) in
                let uu____4318 = is_type g t in
                if uu____4318
                then
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
                else
                  (let head2 = FStar_Syntax_Util.un_uinst head1 in
                   match head2.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_name uu____4327 ->
                       let uu____4328 =
                         let uu____4335 =
                           FStar_Extraction_ML_UEnv.lookup_term g head2 in
                         match uu____4335 with
                         | (FStar_Util.Inr (uu____4345,x1,x2,x3),q) ->
                             ((x1, x2, x3), q)
                         | uu____4370 -> failwith "FIXME Ty" in
                       (match uu____4328 with
                        | ((head_ml,(vars,t1),inst_ok),qual) ->
                            let has_typ_apps =
                              match args with
                              | (a,uu____4399)::uu____4400 -> is_type g a
                              | uu____4414 -> false in
                            let uu____4420 =
                              match vars with
                              | uu____4437::uu____4438 when
                                  (Prims.op_Negation has_typ_apps) && inst_ok
                                  -> (head_ml, t1, args)
                              | uu____4445 ->
                                  let n1 = FStar_List.length vars in
                                  if n1 <= (FStar_List.length args)
                                  then
                                    let uu____4471 =
                                      FStar_Util.first_N n1 args in
                                    (match uu____4471 with
                                     | (prefix1,rest) ->
                                         let prefixAsMLTypes =
                                           FStar_List.map
                                             (fun uu____4526  ->
                                                match uu____4526 with
                                                | (x,uu____4530) ->
                                                    term_as_mlty g x) prefix1 in
                                         let t2 =
                                           instantiate (vars, t1)
                                             prefixAsMLTypes in
                                         let head3 =
                                           match head_ml.FStar_Extraction_ML_Syntax.expr
                                           with
                                           | FStar_Extraction_ML_Syntax.MLE_Name
                                               uu____4533 ->
                                               let uu___144_4534 = head_ml in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (uu___144_4534.FStar_Extraction_ML_Syntax.expr);
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   = t2;
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___144_4534.FStar_Extraction_ML_Syntax.loc)
                                               }
                                           | FStar_Extraction_ML_Syntax.MLE_Var
                                               uu____4535 ->
                                               let uu___144_4536 = head_ml in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (uu___144_4536.FStar_Extraction_ML_Syntax.expr);
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   = t2;
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___144_4536.FStar_Extraction_ML_Syntax.loc)
                                               }
                                           | FStar_Extraction_ML_Syntax.MLE_App
                                               (head3,{
                                                        FStar_Extraction_ML_Syntax.expr
                                                          =
                                                          FStar_Extraction_ML_Syntax.MLE_Const
                                                          (FStar_Extraction_ML_Syntax.MLC_Unit
                                                          );
                                                        FStar_Extraction_ML_Syntax.mlty
                                                          = uu____4538;
                                                        FStar_Extraction_ML_Syntax.loc
                                                          = uu____4539;_}::[])
                                               ->
                                               FStar_All.pipe_right
                                                 (FStar_Extraction_ML_Syntax.MLE_App
                                                    ((let uu___145_4542 =
                                                        head3 in
                                                      {
                                                        FStar_Extraction_ML_Syntax.expr
                                                          =
                                                          (uu___145_4542.FStar_Extraction_ML_Syntax.expr);
                                                        FStar_Extraction_ML_Syntax.mlty
                                                          =
                                                          (FStar_Extraction_ML_Syntax.MLTY_Fun
                                                             (FStar_Extraction_ML_Syntax.ml_unit_ty,
                                                               FStar_Extraction_ML_Syntax.E_PURE,
                                                               t2));
                                                        FStar_Extraction_ML_Syntax.loc
                                                          =
                                                          (uu___145_4542.FStar_Extraction_ML_Syntax.loc)
                                                      }),
                                                      [FStar_Extraction_ML_Syntax.ml_unit]))
                                                 (FStar_Extraction_ML_Syntax.with_ty
                                                    t2)
                                           | uu____4543 ->
                                               failwith
                                                 "Impossible: Unexpected head term" in
                                         (head3, t2, rest))
                                  else err_uninst g head2 (vars, t1) top in
                            (match uu____4420 with
                             | (head_ml1,head_t,args1) ->
                                 (match args1 with
                                  | [] ->
                                      let uu____4581 =
                                        maybe_eta_data_and_project_record g
                                          qual head_t head_ml1 in
                                      (uu____4581,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        head_t)
                                  | uu____4582 ->
                                      extract_app_maybe_projector qual
                                        head_ml1
                                        (FStar_Extraction_ML_Syntax.E_PURE,
                                          head_t) args1)))
                   | FStar_Syntax_Syntax.Tm_fvar uu____4588 ->
                       let uu____4589 =
                         let uu____4596 =
                           FStar_Extraction_ML_UEnv.lookup_term g head2 in
                         match uu____4596 with
                         | (FStar_Util.Inr (uu____4606,x1,x2,x3),q) ->
                             ((x1, x2, x3), q)
                         | uu____4631 -> failwith "FIXME Ty" in
                       (match uu____4589 with
                        | ((head_ml,(vars,t1),inst_ok),qual) ->
                            let has_typ_apps =
                              match args with
                              | (a,uu____4660)::uu____4661 -> is_type g a
                              | uu____4675 -> false in
                            let uu____4681 =
                              match vars with
                              | uu____4698::uu____4699 when
                                  (Prims.op_Negation has_typ_apps) && inst_ok
                                  -> (head_ml, t1, args)
                              | uu____4706 ->
                                  let n1 = FStar_List.length vars in
                                  if n1 <= (FStar_List.length args)
                                  then
                                    let uu____4732 =
                                      FStar_Util.first_N n1 args in
                                    (match uu____4732 with
                                     | (prefix1,rest) ->
                                         let prefixAsMLTypes =
                                           FStar_List.map
                                             (fun uu____4787  ->
                                                match uu____4787 with
                                                | (x,uu____4791) ->
                                                    term_as_mlty g x) prefix1 in
                                         let t2 =
                                           instantiate (vars, t1)
                                             prefixAsMLTypes in
                                         let head3 =
                                           match head_ml.FStar_Extraction_ML_Syntax.expr
                                           with
                                           | FStar_Extraction_ML_Syntax.MLE_Name
                                               uu____4794 ->
                                               let uu___144_4795 = head_ml in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (uu___144_4795.FStar_Extraction_ML_Syntax.expr);
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   = t2;
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___144_4795.FStar_Extraction_ML_Syntax.loc)
                                               }
                                           | FStar_Extraction_ML_Syntax.MLE_Var
                                               uu____4796 ->
                                               let uu___144_4797 = head_ml in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (uu___144_4797.FStar_Extraction_ML_Syntax.expr);
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   = t2;
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___144_4797.FStar_Extraction_ML_Syntax.loc)
                                               }
                                           | FStar_Extraction_ML_Syntax.MLE_App
                                               (head3,{
                                                        FStar_Extraction_ML_Syntax.expr
                                                          =
                                                          FStar_Extraction_ML_Syntax.MLE_Const
                                                          (FStar_Extraction_ML_Syntax.MLC_Unit
                                                          );
                                                        FStar_Extraction_ML_Syntax.mlty
                                                          = uu____4799;
                                                        FStar_Extraction_ML_Syntax.loc
                                                          = uu____4800;_}::[])
                                               ->
                                               FStar_All.pipe_right
                                                 (FStar_Extraction_ML_Syntax.MLE_App
                                                    ((let uu___145_4803 =
                                                        head3 in
                                                      {
                                                        FStar_Extraction_ML_Syntax.expr
                                                          =
                                                          (uu___145_4803.FStar_Extraction_ML_Syntax.expr);
                                                        FStar_Extraction_ML_Syntax.mlty
                                                          =
                                                          (FStar_Extraction_ML_Syntax.MLTY_Fun
                                                             (FStar_Extraction_ML_Syntax.ml_unit_ty,
                                                               FStar_Extraction_ML_Syntax.E_PURE,
                                                               t2));
                                                        FStar_Extraction_ML_Syntax.loc
                                                          =
                                                          (uu___145_4803.FStar_Extraction_ML_Syntax.loc)
                                                      }),
                                                      [FStar_Extraction_ML_Syntax.ml_unit]))
                                                 (FStar_Extraction_ML_Syntax.with_ty
                                                    t2)
                                           | uu____4804 ->
                                               failwith
                                                 "Impossible: Unexpected head term" in
                                         (head3, t2, rest))
                                  else err_uninst g head2 (vars, t1) top in
                            (match uu____4681 with
                             | (head_ml1,head_t,args1) ->
                                 (match args1 with
                                  | [] ->
                                      let uu____4842 =
                                        maybe_eta_data_and_project_record g
                                          qual head_t head_ml1 in
                                      (uu____4842,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        head_t)
                                  | uu____4843 ->
                                      extract_app_maybe_projector qual
                                        head_ml1
                                        (FStar_Extraction_ML_Syntax.E_PURE,
                                          head_t) args1)))
                   | uu____4849 ->
                       let uu____4850 = term_as_mlexpr g head2 in
                       (match uu____4850 with
                        | (head3,f,t1) ->
                            extract_app_maybe_projector None head3 (f, t1)
                              args)))
       | FStar_Syntax_Syntax.Tm_ascribed (e0,(tc,uu____4862),f) ->
           let t1 =
             match tc with
             | FStar_Util.Inl t1 -> term_as_mlty g t1
             | FStar_Util.Inr c ->
                 term_as_mlty g (FStar_Syntax_Util.comp_result c) in
           let f1 =
             match f with
             | None  -> failwith "Ascription node with an empty effect label"
             | Some l -> effect_as_etag g l in
           let uu____4916 = check_term_as_mlexpr g e0 f1 t1 in
           (match uu____4916 with | (e,t2) -> (e, f1, t2))
       | FStar_Syntax_Syntax.Tm_let ((is_rec,lbs),e') ->
           let top_level = FStar_Syntax_Syntax.is_top_level lbs in
           let uu____4937 =
             if is_rec
             then FStar_Syntax_Subst.open_let_rec lbs e'
             else
               (let uu____4945 = FStar_Syntax_Syntax.is_top_level lbs in
                if uu____4945
                then (lbs, e')
                else
                  (let lb = FStar_List.hd lbs in
                   let x =
                     let uu____4955 =
                       FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                     FStar_Syntax_Syntax.freshen_bv uu____4955 in
                   let lb1 =
                     let uu___146_4957 = lb in
                     {
                       FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                       FStar_Syntax_Syntax.lbunivs =
                         (uu___146_4957.FStar_Syntax_Syntax.lbunivs);
                       FStar_Syntax_Syntax.lbtyp =
                         (uu___146_4957.FStar_Syntax_Syntax.lbtyp);
                       FStar_Syntax_Syntax.lbeff =
                         (uu___146_4957.FStar_Syntax_Syntax.lbeff);
                       FStar_Syntax_Syntax.lbdef =
                         (uu___146_4957.FStar_Syntax_Syntax.lbdef)
                     } in
                   let e'1 =
                     FStar_Syntax_Subst.subst
                       [FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x)] e' in
                   ([lb1], e'1))) in
           (match uu____4937 with
            | (lbs1,e'1) ->
                let lbs2 =
                  if top_level
                  then
                    FStar_All.pipe_right lbs1
                      (FStar_List.map
                         (fun lb  ->
                            let tcenv =
                              let uu____4974 =
                                FStar_Ident.lid_of_path
                                  (FStar_List.append
                                     (fst
                                        g.FStar_Extraction_ML_UEnv.currentModule)
                                     [snd
                                        g.FStar_Extraction_ML_UEnv.currentModule])
                                  FStar_Range.dummyRange in
                              FStar_TypeChecker_Env.set_current_module
                                g.FStar_Extraction_ML_UEnv.tcenv uu____4974 in
                            FStar_Extraction_ML_UEnv.debug g
                              (fun uu____4978  ->
                                 FStar_Options.set_option "debug_level"
                                   (FStar_Options.List
                                      [FStar_Options.String "Norm";
                                      FStar_Options.String "Extraction"]));
                            (let lbdef =
                               let uu____4982 = FStar_Options.ml_ish () in
                               if uu____4982
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
                             let uu___147_4986 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___147_4986.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___147_4986.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___147_4986.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___147_4986.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef
                             })))
                  else lbs1 in
                let maybe_generalize uu____5000 =
                  match uu____5000 with
                  | { FStar_Syntax_Syntax.lbname = lbname_;
                      FStar_Syntax_Syntax.lbunivs = uu____5011;
                      FStar_Syntax_Syntax.lbtyp = t1;
                      FStar_Syntax_Syntax.lbeff = lbeff;
                      FStar_Syntax_Syntax.lbdef = e;_} ->
                      let f_e = effect_as_etag g lbeff in
                      let t2 = FStar_Syntax_Subst.compress t1 in
                      (match t2.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                           let uu____5054 = FStar_List.hd bs in
                           FStar_All.pipe_right uu____5054 (is_type_binder g)
                           ->
                           let uu____5061 = FStar_Syntax_Subst.open_comp bs c in
                           (match uu____5061 with
                            | (bs1,c1) ->
                                let uu____5075 =
                                  let uu____5080 =
                                    FStar_Util.prefix_until
                                      (fun x  ->
                                         let uu____5098 = is_type_binder g x in
                                         Prims.op_Negation uu____5098) bs1 in
                                  match uu____5080 with
                                  | None  ->
                                      (bs1,
                                        (FStar_Syntax_Util.comp_result c1))
                                  | Some (bs2,b,rest) ->
                                      let uu____5146 =
                                        FStar_Syntax_Util.arrow (b :: rest)
                                          c1 in
                                      (bs2, uu____5146) in
                                (match uu____5075 with
                                 | (tbinders,tbody) ->
                                     let n_tbinders =
                                       FStar_List.length tbinders in
                                     let e1 =
                                       let uu____5177 = normalize_abs e in
                                       FStar_All.pipe_right uu____5177
                                         FStar_Syntax_Util.unmeta in
                                     (match e1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Tm_abs
                                          (bs2,body,copt) ->
                                          let uu____5212 =
                                            FStar_Syntax_Subst.open_term bs2
                                              body in
                                          (match uu____5212 with
                                           | (bs3,body1) ->
                                               if
                                                 n_tbinders <=
                                                   (FStar_List.length bs3)
                                               then
                                                 let uu____5247 =
                                                   FStar_Util.first_N
                                                     n_tbinders bs3 in
                                                 (match uu____5247 with
                                                  | (targs,rest_args) ->
                                                      let expected_source_ty
                                                        =
                                                        let s =
                                                          FStar_List.map2
                                                            (fun uu____5292 
                                                               ->
                                                               fun uu____5293
                                                                  ->
                                                                 match 
                                                                   (uu____5292,
                                                                    uu____5293)
                                                                 with
                                                                 | ((x,uu____5303),
                                                                    (y,uu____5305))
                                                                    ->
                                                                    let uu____5310
                                                                    =
                                                                    let uu____5315
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    y in
                                                                    (x,
                                                                    uu____5315) in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____5310)
                                                            tbinders targs in
                                                        FStar_Syntax_Subst.subst
                                                          s tbody in
                                                      let env =
                                                        FStar_List.fold_left
                                                          (fun env  ->
                                                             fun uu____5320 
                                                               ->
                                                               match uu____5320
                                                               with
                                                               | (a,uu____5324)
                                                                   ->
                                                                   FStar_Extraction_ML_UEnv.extend_ty
                                                                    env a
                                                                    None) g
                                                          targs in
                                                      let expected_t =
                                                        term_as_mlty env
                                                          expected_source_ty in
                                                      let polytype =
                                                        let uu____5332 =
                                                          FStar_All.pipe_right
                                                            targs
                                                            (FStar_List.map
                                                               (fun
                                                                  uu____5346 
                                                                  ->
                                                                  match uu____5346
                                                                  with
                                                                  | (x,uu____5352)
                                                                    ->
                                                                    FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                                    x)) in
                                                        (uu____5332,
                                                          expected_t) in
                                                      let add_unit =
                                                        match rest_args with
                                                        | [] ->
                                                            let uu____5359 =
                                                              is_fstar_value
                                                                body1 in
                                                            Prims.op_Negation
                                                              uu____5359
                                                        | uu____5360 -> false in
                                                      let rest_args1 =
                                                        if add_unit
                                                        then unit_binder ::
                                                          rest_args
                                                        else rest_args in
                                                      let body2 =
                                                        match rest_args1 with
                                                        | [] -> body1
                                                        | uu____5369 ->
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
                                          uu____5413 ->
                                          let env =
                                            FStar_List.fold_left
                                              (fun env  ->
                                                 fun uu____5422  ->
                                                   match uu____5422 with
                                                   | (a,uu____5426) ->
                                                       FStar_Extraction_ML_UEnv.extend_ty
                                                         env a None) g
                                              tbinders in
                                          let expected_t =
                                            term_as_mlty env tbody in
                                          let polytype =
                                            let uu____5434 =
                                              FStar_All.pipe_right tbinders
                                                (FStar_List.map
                                                   (fun uu____5445  ->
                                                      match uu____5445 with
                                                      | (x,uu____5451) ->
                                                          FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                            x)) in
                                            (uu____5434, expected_t) in
                                          let args =
                                            FStar_All.pipe_right tbinders
                                              (FStar_List.map
                                                 (fun uu____5460  ->
                                                    match uu____5460 with
                                                    | (bv,uu____5464) ->
                                                        let uu____5465 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            bv in
                                                        FStar_All.pipe_right
                                                          uu____5465
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
                                          uu____5499 ->
                                          let env =
                                            FStar_List.fold_left
                                              (fun env  ->
                                                 fun uu____5504  ->
                                                   match uu____5504 with
                                                   | (a,uu____5508) ->
                                                       FStar_Extraction_ML_UEnv.extend_ty
                                                         env a None) g
                                              tbinders in
                                          let expected_t =
                                            term_as_mlty env tbody in
                                          let polytype =
                                            let uu____5516 =
                                              FStar_All.pipe_right tbinders
                                                (FStar_List.map
                                                   (fun uu____5527  ->
                                                      match uu____5527 with
                                                      | (x,uu____5533) ->
                                                          FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                            x)) in
                                            (uu____5516, expected_t) in
                                          let args =
                                            FStar_All.pipe_right tbinders
                                              (FStar_List.map
                                                 (fun uu____5542  ->
                                                    match uu____5542 with
                                                    | (bv,uu____5546) ->
                                                        let uu____5547 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            bv in
                                                        FStar_All.pipe_right
                                                          uu____5547
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
                                          uu____5581 ->
                                          let env =
                                            FStar_List.fold_left
                                              (fun env  ->
                                                 fun uu____5586  ->
                                                   match uu____5586 with
                                                   | (a,uu____5590) ->
                                                       FStar_Extraction_ML_UEnv.extend_ty
                                                         env a None) g
                                              tbinders in
                                          let expected_t =
                                            term_as_mlty env tbody in
                                          let polytype =
                                            let uu____5598 =
                                              FStar_All.pipe_right tbinders
                                                (FStar_List.map
                                                   (fun uu____5609  ->
                                                      match uu____5609 with
                                                      | (x,uu____5615) ->
                                                          FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                            x)) in
                                            (uu____5598, expected_t) in
                                          let args =
                                            FStar_All.pipe_right tbinders
                                              (FStar_List.map
                                                 (fun uu____5624  ->
                                                    match uu____5624 with
                                                    | (bv,uu____5628) ->
                                                        let uu____5629 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            bv in
                                                        FStar_All.pipe_right
                                                          uu____5629
                                                          FStar_Syntax_Syntax.as_arg)) in
                                          let e2 =
                                            FStar_Syntax_Syntax.mk
                                              (FStar_Syntax_Syntax.Tm_app
                                                 (e1, args)) None
                                              e1.FStar_Syntax_Syntax.pos in
                                          (lbname_, f_e,
                                            (t2, (tbinders, polytype)),
                                            false, e2)
                                      | uu____5663 ->
                                          err_value_restriction e1)))
                       | uu____5673 ->
                           let expected_t = term_as_mlty g t2 in
                           (lbname_, f_e, (t2, ([], ([], expected_t))),
                             false, e)) in
                let check_lb env uu____5730 =
                  match uu____5730 with
                  | (nm,(lbname,f,(t1,(targs,polytype)),add_unit,e)) ->
                      let env1 =
                        FStar_List.fold_left
                          (fun env1  ->
                             fun uu____5801  ->
                               match uu____5801 with
                               | (a,uu____5805) ->
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
                      let uu____5808 =
                        check_term_as_mlexpr env1 e f expected_t in
                      (match uu____5808 with
                       | (e1,uu____5814) ->
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
                let uu____5849 =
                  FStar_List.fold_right
                    (fun lb  ->
                       fun uu____5888  ->
                         match uu____5888 with
                         | (env,lbs4) ->
                             let uu____5952 = lb in
                             (match uu____5952 with
                              | (lbname,uu____5977,(t1,(uu____5979,polytype)),add_unit,uu____5982)
                                  ->
                                  let uu____5989 =
                                    FStar_Extraction_ML_UEnv.extend_lb env
                                      lbname t1 polytype add_unit true in
                                  (match uu____5989 with
                                   | (env1,nm) -> (env1, ((nm, lb) :: lbs4)))))
                    lbs3 (g, []) in
                (match uu____5849 with
                 | (env_body,lbs4) ->
                     let env_def = if is_rec then env_body else g in
                     let lbs5 =
                       FStar_All.pipe_right lbs4
                         (FStar_List.map (check_lb env_def)) in
                     let e'_rng = e'1.FStar_Syntax_Syntax.pos in
                     let uu____6132 = term_as_mlexpr env_body e'1 in
                     (match uu____6132 with
                      | (e'2,f',t') ->
                          let f =
                            let uu____6143 =
                              let uu____6145 =
                                FStar_List.map FStar_Pervasives.fst lbs5 in
                              f' :: uu____6145 in
                            FStar_Extraction_ML_Util.join_l e'_rng uu____6143 in
                          let is_rec1 =
                            if is_rec = true
                            then FStar_Extraction_ML_Syntax.Rec
                            else FStar_Extraction_ML_Syntax.NonRec in
                          let uu____6151 =
                            let uu____6152 =
                              let uu____6153 =
                                let uu____6154 =
                                  FStar_List.map FStar_Pervasives.snd lbs5 in
                                (is_rec1, [], uu____6154) in
                              mk_MLE_Let top_level uu____6153 e'2 in
                            let uu____6160 =
                              FStar_Extraction_ML_Util.mlloc_of_range
                                t.FStar_Syntax_Syntax.pos in
                            FStar_Extraction_ML_Syntax.with_ty_loc t'
                              uu____6152 uu____6160 in
                          (uu____6151, f, t'))))
       | FStar_Syntax_Syntax.Tm_match (scrutinee,pats) ->
           let uu____6189 = term_as_mlexpr g scrutinee in
           (match uu____6189 with
            | (e,f_e,t_e) ->
                let uu____6199 = check_pats_for_ite pats in
                (match uu____6199 with
                 | (b,then_e,else_e) ->
                     let no_lift x t1 = x in
                     if b
                     then
                       (match (then_e, else_e) with
                        | (Some then_e1,Some else_e1) ->
                            let uu____6234 = term_as_mlexpr g then_e1 in
                            (match uu____6234 with
                             | (then_mle,f_then,t_then) ->
                                 let uu____6244 = term_as_mlexpr g else_e1 in
                                 (match uu____6244 with
                                  | (else_mle,f_else,t_else) ->
                                      let uu____6254 =
                                        let uu____6261 =
                                          type_leq g t_then t_else in
                                        if uu____6261
                                        then (t_else, no_lift)
                                        else
                                          (let uu____6273 =
                                             type_leq g t_else t_then in
                                           if uu____6273
                                           then (t_then, no_lift)
                                           else
                                             (FStar_Extraction_ML_Syntax.MLTY_Top,
                                               FStar_Extraction_ML_Syntax.apply_obj_repr)) in
                                      (match uu____6254 with
                                       | (t_branch,maybe_lift1) ->
                                           let uu____6302 =
                                             let uu____6303 =
                                               let uu____6304 =
                                                 let uu____6309 =
                                                   maybe_lift1 then_mle
                                                     t_then in
                                                 let uu____6310 =
                                                   let uu____6312 =
                                                     maybe_lift1 else_mle
                                                       t_else in
                                                   Some uu____6312 in
                                                 (e, uu____6309, uu____6310) in
                                               FStar_Extraction_ML_Syntax.MLE_If
                                                 uu____6304 in
                                             FStar_All.pipe_left
                                               (FStar_Extraction_ML_Syntax.with_ty
                                                  t_branch) uu____6303 in
                                           let uu____6314 =
                                             FStar_Extraction_ML_Util.join
                                               then_e1.FStar_Syntax_Syntax.pos
                                               f_then f_else in
                                           (uu____6302, uu____6314, t_branch))))
                        | uu____6315 ->
                            failwith
                              "ITE pats matched but then and else expressions not found?")
                     else
                       (let uu____6324 =
                          FStar_All.pipe_right pats
                            (FStar_Util.fold_map
                               (fun compat  ->
                                  fun br  ->
                                    let uu____6374 =
                                      FStar_Syntax_Subst.open_branch br in
                                    match uu____6374 with
                                    | (pat,when_opt,branch1) ->
                                        let uu____6404 =
                                          extract_pat g pat t_e in
                                        (match uu____6404 with
                                         | (env,p,pat_t_compat) ->
                                             let uu____6435 =
                                               match when_opt with
                                               | None  ->
                                                   (None,
                                                     FStar_Extraction_ML_Syntax.E_PURE)
                                               | Some w ->
                                                   let uu____6450 =
                                                     term_as_mlexpr env w in
                                                   (match uu____6450 with
                                                    | (w1,f_w,t_w) ->
                                                        let w2 =
                                                          maybe_coerce env w1
                                                            t_w
                                                            FStar_Extraction_ML_Syntax.ml_bool_ty in
                                                        ((Some w2), f_w)) in
                                             (match uu____6435 with
                                              | (when_opt1,f_when) ->
                                                  let uu____6478 =
                                                    term_as_mlexpr env
                                                      branch1 in
                                                  (match uu____6478 with
                                                   | (mlbranch,f_branch,t_branch)
                                                       ->
                                                       let uu____6497 =
                                                         FStar_All.pipe_right
                                                           p
                                                           (FStar_List.map
                                                              (fun uu____6534
                                                                  ->
                                                                 match uu____6534
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
                                                         uu____6497))))) true) in
                        match uu____6324 with
                        | (pat_t_compat,mlbranches) ->
                            let mlbranches1 = FStar_List.flatten mlbranches in
                            let e1 =
                              if pat_t_compat
                              then e
                              else
                                (FStar_Extraction_ML_UEnv.debug g
                                   (fun uu____6620  ->
                                      let uu____6621 =
                                        FStar_Extraction_ML_Code.string_of_mlexpr
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          e in
                                      let uu____6622 =
                                        FStar_Extraction_ML_Code.string_of_mlty
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          t_e in
                                      FStar_Util.print2
                                        "Coercing scrutinee %s from type %s because pattern type is incompatible\n"
                                        uu____6621 uu____6622);
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty t_e)
                                   (FStar_Extraction_ML_Syntax.MLE_Coerce
                                      (e, t_e,
                                        FStar_Extraction_ML_Syntax.MLTY_Top))) in
                            (match mlbranches1 with
                             | [] ->
                                 let uu____6635 =
                                   let uu____6640 =
                                     let uu____6649 =
                                       FStar_Syntax_Syntax.lid_as_fv
                                         FStar_Syntax_Const.failwith_lid
                                         FStar_Syntax_Syntax.Delta_constant
                                         None in
                                     FStar_Extraction_ML_UEnv.lookup_fv g
                                       uu____6649 in
                                   FStar_All.pipe_left FStar_Util.right
                                     uu____6640 in
                                 (match uu____6635 with
                                  | (uu____6671,fw,uu____6673,uu____6674) ->
                                      let uu____6675 =
                                        let uu____6676 =
                                          let uu____6677 =
                                            let uu____6681 =
                                              let uu____6683 =
                                                FStar_All.pipe_left
                                                  (FStar_Extraction_ML_Syntax.with_ty
                                                     FStar_Extraction_ML_Syntax.ml_string_ty)
                                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                                     (FStar_Extraction_ML_Syntax.MLC_String
                                                        "unreachable")) in
                                              [uu____6683] in
                                            (fw, uu____6681) in
                                          FStar_Extraction_ML_Syntax.MLE_App
                                            uu____6677 in
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             FStar_Extraction_ML_Syntax.ml_unit_ty)
                                          uu____6676 in
                                      (uu____6675,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        FStar_Extraction_ML_Syntax.ml_unit_ty))
                             | (uu____6685,uu____6686,(uu____6687,f_first,t_first))::rest
                                 ->
                                 let uu____6719 =
                                   FStar_List.fold_left
                                     (fun uu____6735  ->
                                        fun uu____6736  ->
                                          match (uu____6735, uu____6736) with
                                          | ((topt,f),(uu____6766,uu____6767,
                                                       (uu____6768,f_branch,t_branch)))
                                              ->
                                              let f1 =
                                                FStar_Extraction_ML_Util.join
                                                  top.FStar_Syntax_Syntax.pos
                                                  f f_branch in
                                              let topt1 =
                                                match topt with
                                                | None  -> None
                                                | Some t1 ->
                                                    let uu____6799 =
                                                      type_leq g t1 t_branch in
                                                    if uu____6799
                                                    then Some t_branch
                                                    else
                                                      (let uu____6802 =
                                                         type_leq g t_branch
                                                           t1 in
                                                       if uu____6802
                                                       then Some t1
                                                       else None) in
                                              (topt1, f1))
                                     ((Some t_first), f_first) rest in
                                 (match uu____6719 with
                                  | (topt,f_match) ->
                                      let mlbranches2 =
                                        FStar_All.pipe_right mlbranches1
                                          (FStar_List.map
                                             (fun uu____6848  ->
                                                match uu____6848 with
                                                | (p,(wopt,uu____6864),
                                                   (b1,uu____6866,t1)) ->
                                                    let b2 =
                                                      match topt with
                                                      | None  ->
                                                          FStar_Extraction_ML_Syntax.apply_obj_repr
                                                            b1 t1
                                                      | Some uu____6877 -> b1 in
                                                    (p, wopt, b2))) in
                                      let t_match =
                                        match topt with
                                        | None  ->
                                            FStar_Extraction_ML_Syntax.MLTY_Top
                                        | Some t1 -> t1 in
                                      let uu____6881 =
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             t_match)
                                          (FStar_Extraction_ML_Syntax.MLE_Match
                                             (e1, mlbranches2)) in
                                      (uu____6881, f_match, t_match)))))))
let fresh: Prims.string -> (Prims.string* Prims.int) =
  let c = FStar_Util.mk_ref (Prims.parse_int "0") in
  fun x  ->
    FStar_Util.incr c; (let uu____6899 = FStar_ST.read c in (x, uu____6899))
let ind_discriminator_body:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlmodule1
  =
  fun env  ->
    fun discName  ->
      fun constrName  ->
        let uu____6911 =
          let uu____6914 =
            FStar_TypeChecker_Env.lookup_lid
              env.FStar_Extraction_ML_UEnv.tcenv discName in
          FStar_All.pipe_left FStar_Pervasives.fst uu____6914 in
        match uu____6911 with
        | (uu____6927,fstar_disc_type) ->
            let wildcards =
              let uu____6935 =
                let uu____6936 = FStar_Syntax_Subst.compress fstar_disc_type in
                uu____6936.FStar_Syntax_Syntax.n in
              match uu____6935 with
              | FStar_Syntax_Syntax.Tm_arrow (binders,uu____6945) ->
                  let uu____6956 =
                    FStar_All.pipe_right binders
                      (FStar_List.filter
                         (fun uu___141_6971  ->
                            match uu___141_6971 with
                            | (uu____6975,Some (FStar_Syntax_Syntax.Implicit
                               uu____6976)) -> true
                            | uu____6978 -> false)) in
                  FStar_All.pipe_right uu____6956
                    (FStar_List.map
                       (fun uu____6998  ->
                          let uu____7002 = fresh "_" in
                          (uu____7002, FStar_Extraction_ML_Syntax.MLTY_Top)))
              | uu____7007 -> failwith "Discriminator must be a function" in
            let mlid = fresh "_discr_" in
            let targ = FStar_Extraction_ML_Syntax.MLTY_Top in
            let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top in
            let discrBody =
              let uu____7019 =
                let uu____7020 =
                  let uu____7026 =
                    let uu____7027 =
                      let uu____7028 =
                        let uu____7036 =
                          let uu____7037 =
                            let uu____7038 =
                              let uu____7039 =
                                FStar_Extraction_ML_Syntax.idsym mlid in
                              ([], uu____7039) in
                            FStar_Extraction_ML_Syntax.MLE_Name uu____7038 in
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty targ)
                            uu____7037 in
                        let uu____7041 =
                          let uu____7047 =
                            let uu____7052 =
                              let uu____7053 =
                                let uu____7057 =
                                  FStar_Extraction_ML_Syntax.mlpath_of_lident
                                    constrName in
                                (uu____7057,
                                  [FStar_Extraction_ML_Syntax.MLP_Wild]) in
                              FStar_Extraction_ML_Syntax.MLP_CTor uu____7053 in
                            let uu____7059 =
                              FStar_All.pipe_left
                                (FStar_Extraction_ML_Syntax.with_ty
                                   FStar_Extraction_ML_Syntax.ml_bool_ty)
                                (FStar_Extraction_ML_Syntax.MLE_Const
                                   (FStar_Extraction_ML_Syntax.MLC_Bool true)) in
                            (uu____7052, None, uu____7059) in
                          let uu____7061 =
                            let uu____7067 =
                              let uu____7072 =
                                FStar_All.pipe_left
                                  (FStar_Extraction_ML_Syntax.with_ty
                                     FStar_Extraction_ML_Syntax.ml_bool_ty)
                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                     (FStar_Extraction_ML_Syntax.MLC_Bool
                                        false)) in
                              (FStar_Extraction_ML_Syntax.MLP_Wild, None,
                                uu____7072) in
                            [uu____7067] in
                          uu____7047 :: uu____7061 in
                        (uu____7036, uu____7041) in
                      FStar_Extraction_ML_Syntax.MLE_Match uu____7028 in
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.ml_bool_ty) uu____7027 in
                  ((FStar_List.append wildcards [(mlid, targ)]), uu____7026) in
                FStar_Extraction_ML_Syntax.MLE_Fun uu____7020 in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty disc_ty) uu____7019 in
            let uu____7110 =
              let uu____7111 =
                let uu____7113 =
                  let uu____7114 =
                    FStar_Extraction_ML_UEnv.convIdent
                      discName.FStar_Ident.ident in
                  {
                    FStar_Extraction_ML_Syntax.mllb_name = uu____7114;
                    FStar_Extraction_ML_Syntax.mllb_tysc = None;
                    FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                    FStar_Extraction_ML_Syntax.mllb_def = discrBody;
                    FStar_Extraction_ML_Syntax.print_typ = false
                  } in
                [uu____7113] in
              (FStar_Extraction_ML_Syntax.NonRec, [], uu____7111) in
            FStar_Extraction_ML_Syntax.MLM_Let uu____7110