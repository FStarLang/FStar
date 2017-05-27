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
      (let uu____1087 = FStar_List.hd l in
       match uu____1087 with
       | (p1,w1,e1) ->
           let uu____1106 =
             let uu____1111 = FStar_List.tl l in FStar_List.hd uu____1111 in
           (match uu____1106 with
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
                 | uu____1150 -> def)))
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
            let uu____1193 = erasable g f ty in
            if uu____1193
            then
              let uu____1194 =
                type_leq g ty FStar_Extraction_ML_Syntax.ml_unit_ty in
              (if uu____1194
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
          let uu____1210 = type_leq_c g (Some e) ty1 expect in
          match uu____1210 with
          | (true ,Some e') -> e'
          | uu____1216 ->
              (FStar_Extraction_ML_UEnv.debug g
                 (fun uu____1221  ->
                    let uu____1222 =
                      FStar_Extraction_ML_Code.string_of_mlexpr
                        g.FStar_Extraction_ML_UEnv.currentModule e in
                    let uu____1223 =
                      FStar_Extraction_ML_Code.string_of_mlty
                        g.FStar_Extraction_ML_UEnv.currentModule ty1 in
                    let uu____1224 =
                      FStar_Extraction_ML_Code.string_of_mlty
                        g.FStar_Extraction_ML_UEnv.currentModule expect in
                    FStar_Util.print3
                      "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n"
                      uu____1222 uu____1223 uu____1224);
               FStar_All.pipe_left
                 (FStar_Extraction_ML_Syntax.with_ty expect)
                 (FStar_Extraction_ML_Syntax.MLE_Coerce (e, ty1, expect)))
let bv_as_mlty:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlty
  =
  fun g  ->
    fun bv  ->
      let uu____1231 = FStar_Extraction_ML_UEnv.lookup_bv g bv in
      match uu____1231 with
      | FStar_Util.Inl (uu____1232,t) -> t
      | uu____1240 -> FStar_Extraction_ML_Syntax.MLTY_Top
let rec term_as_mlty:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlty
  =
  fun g  ->
    fun t0  ->
      let rec is_top_ty t =
        match t with
        | FStar_Extraction_ML_Syntax.MLTY_Top  -> true
        | FStar_Extraction_ML_Syntax.MLTY_Named uu____1276 ->
            let uu____1280 = FStar_Extraction_ML_Util.udelta_unfold g t in
            (match uu____1280 with | None  -> false | Some t1 -> is_top_ty t1)
        | uu____1283 -> false in
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
      let uu____1286 = is_top_ty mlt in
      if uu____1286
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
      | FStar_Syntax_Syntax.Tm_bvar uu____1292 ->
          let uu____1293 =
            let uu____1294 = FStar_Syntax_Print.term_to_string t1 in
            FStar_Util.format1 "Impossible: Unexpected term %s" uu____1294 in
          failwith uu____1293
      | FStar_Syntax_Syntax.Tm_delayed uu____1295 ->
          let uu____1316 =
            let uu____1317 = FStar_Syntax_Print.term_to_string t1 in
            FStar_Util.format1 "Impossible: Unexpected term %s" uu____1317 in
          failwith uu____1316
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____1318 =
            let uu____1319 = FStar_Syntax_Print.term_to_string t1 in
            FStar_Util.format1 "Impossible: Unexpected term %s" uu____1319 in
          failwith uu____1318
      | FStar_Syntax_Syntax.Tm_constant uu____1320 ->
          FStar_Extraction_ML_UEnv.unknownType
      | FStar_Syntax_Syntax.Tm_uvar uu____1321 ->
          FStar_Extraction_ML_UEnv.unknownType
      | FStar_Syntax_Syntax.Tm_meta (t2,uu____1331) -> term_as_mlty' env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____1336;
             FStar_Syntax_Syntax.index = uu____1337;
             FStar_Syntax_Syntax.sort = t2;_},uu____1339)
          -> term_as_mlty' env t2
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____1347) -> term_as_mlty' env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____1353,uu____1354) ->
          term_as_mlty' env t2
      | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
      | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv []
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____1401 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____1401 with
           | (bs1,c1) ->
               let uu____1406 = binders_as_ml_binders env bs1 in
               (match uu____1406 with
                | (mlbs,env1) ->
                    let t_ret =
                      let eff =
                        FStar_TypeChecker_Env.norm_eff_name
                          env1.FStar_Extraction_ML_UEnv.tcenv
                          (FStar_Syntax_Util.comp_effect_name c1) in
                      let uu____1422 =
                        let uu____1426 =
                          FStar_TypeChecker_Env.effect_decl_opt
                            env1.FStar_Extraction_ML_UEnv.tcenv eff in
                        FStar_Util.must uu____1426 in
                      match uu____1422 with
                      | (ed,qualifiers) ->
                          let uu____1438 =
                            FStar_All.pipe_right qualifiers
                              (FStar_List.contains
                                 FStar_Syntax_Syntax.Reifiable) in
                          if uu____1438
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
                    let uu____1444 =
                      FStar_List.fold_right
                        (fun uu____1451  ->
                           fun uu____1452  ->
                             match (uu____1451, uu____1452) with
                             | ((uu____1463,t2),(tag,t')) ->
                                 (FStar_Extraction_ML_Syntax.E_PURE,
                                   (FStar_Extraction_ML_Syntax.MLTY_Fun
                                      (t2, tag, t')))) mlbs (erase1, t_ret) in
                    (match uu____1444 with | (uu____1471,t2) -> t2)))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let res =
            let uu____1490 =
              let uu____1491 = FStar_Syntax_Util.un_uinst head1 in
              uu____1491.FStar_Syntax_Syntax.n in
            match uu____1490 with
            | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
            | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv args
            | FStar_Syntax_Syntax.Tm_app (head2,args') ->
                let uu____1512 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app
                       (head2, (FStar_List.append args' args))) None
                    t1.FStar_Syntax_Syntax.pos in
                term_as_mlty' env uu____1512
            | uu____1528 -> FStar_Extraction_ML_UEnv.unknownType in
          res
      | FStar_Syntax_Syntax.Tm_abs (bs,ty,uu____1531) ->
          let uu____1554 = FStar_Syntax_Subst.open_term bs ty in
          (match uu____1554 with
           | (bs1,ty1) ->
               let uu____1559 = binders_as_ml_binders env bs1 in
               (match uu____1559 with | (bts,env1) -> term_as_mlty' env1 ty1))
      | FStar_Syntax_Syntax.Tm_type uu____1573 ->
          FStar_Extraction_ML_UEnv.unknownType
      | FStar_Syntax_Syntax.Tm_let uu____1574 ->
          FStar_Extraction_ML_UEnv.unknownType
      | FStar_Syntax_Syntax.Tm_match uu____1582 ->
          FStar_Extraction_ML_UEnv.unknownType
and arg_as_mlty:
  FStar_Extraction_ML_UEnv.env ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.aqual) ->
      FStar_Extraction_ML_Syntax.mlty
  =
  fun g  ->
    fun uu____1599  ->
      match uu____1599 with
      | (a,uu____1603) ->
          let uu____1604 = is_type g a in
          if uu____1604
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
        let uu____1609 =
          FStar_Syntax_Util.arrow_formals
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.ty in
        match uu____1609 with
        | (formals,t) ->
            let mlargs = FStar_List.map (arg_as_mlty g) args in
            let mlargs1 =
              let n_args = FStar_List.length args in
              if (FStar_List.length formals) > n_args
              then
                let uu____1653 = FStar_Util.first_N n_args formals in
                match uu____1653 with
                | (uu____1667,rest) ->
                    let uu____1681 =
                      FStar_List.map
                        (fun uu____1685  ->
                           FStar_Extraction_ML_UEnv.erasedContent) rest in
                    FStar_List.append mlargs uu____1681
              else mlargs in
            let nm =
              let uu____1690 =
                FStar_Extraction_ML_UEnv.maybe_mangle_type_projector g fv in
              match uu____1690 with
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
      let uu____1705 =
        FStar_All.pipe_right bs
          (FStar_List.fold_left
             (fun uu____1729  ->
                fun b  ->
                  match uu____1729 with
                  | (ml_bs,env) ->
                      let uu____1759 = is_type_binder g b in
                      if uu____1759
                      then
                        let b1 = fst b in
                        let env1 =
                          FStar_Extraction_ML_UEnv.extend_ty env b1
                            (Some FStar_Extraction_ML_Syntax.MLTY_Top) in
                        let ml_b =
                          let uu____1774 =
                            FStar_Extraction_ML_UEnv.bv_as_ml_termvar b1 in
                          (uu____1774, FStar_Extraction_ML_Syntax.ml_unit_ty) in
                        ((ml_b :: ml_bs), env1)
                      else
                        (let b1 = fst b in
                         let t = term_as_mlty env b1.FStar_Syntax_Syntax.sort in
                         let uu____1791 =
                           FStar_Extraction_ML_UEnv.extend_bv env b1 
                             ([], t) false false false in
                         match uu____1791 with
                         | (env1,b2) ->
                             let ml_b =
                               let uu____1809 =
                                 FStar_Extraction_ML_UEnv.removeTick b2 in
                               (uu____1809, t) in
                             ((ml_b :: ml_bs), env1))) ([], g)) in
      match uu____1705 with | (ml_bs,env) -> ((FStar_List.rev ml_bs), env)
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
      | (FStar_Extraction_ML_Syntax.MLE_Seq es1,uu____1869) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (FStar_List.append es1 [e2])
      | (uu____1871,FStar_Extraction_ML_Syntax.MLE_Seq es2) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (e1 :: es2)
      | uu____1874 -> FStar_Extraction_ML_Syntax.MLE_Seq [e1; e2]
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
                    | uu____1896 when
                        (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
                          =
                          FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr
                        -> body.FStar_Extraction_ML_Syntax.expr
                    | uu____1897 ->
                        mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def
                          body)
             | uu____1898 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body))
        | uu____1900 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body)
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
           | uu____1914 ->
               (match q with
                | Some (FStar_Syntax_Syntax.Record_ctor (ty,fns)) ->
                    let path =
                      FStar_List.map FStar_Ident.text_of_id ty.FStar_Ident.ns in
                    let fs = record_fields fns pats in
                    FStar_Extraction_ML_Syntax.MLP_Record (path, fs)
                | uu____1930 -> p))
      | uu____1932 -> p
let rec extract_one_pat:
  Prims.bool ->
    Prims.bool ->
      FStar_Extraction_ML_UEnv.env ->
        FStar_Syntax_Syntax.pat ->
          FStar_Extraction_ML_Syntax.mlty option ->
            (FStar_Extraction_ML_UEnv.env*
              (FStar_Extraction_ML_Syntax.mlpattern*
              FStar_Extraction_ML_Syntax.mlexpr Prims.list) option*
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
                       (fun uu____1971  ->
                          let uu____1972 =
                            FStar_Extraction_ML_Code.string_of_mlty
                              g.FStar_Extraction_ML_UEnv.currentModule t' in
                          let uu____1973 =
                            FStar_Extraction_ML_Code.string_of_mlty
                              g.FStar_Extraction_ML_UEnv.currentModule t in
                          FStar_Util.print2
                            "Expected pattern type %s; got pattern type %s\n"
                            uu____1972 uu____1973)
                   else ();
                   ok) in
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_disj uu____1982 ->
                failwith "Impossible: Nested disjunctive pattern"
            | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int
                (c,None )) ->
                let i = FStar_Const.Const_int (c, None) in
                let x = FStar_Extraction_ML_Syntax.gensym () in
                let when_clause =
                  let uu____2007 =
                    let uu____2008 =
                      let uu____2012 =
                        let uu____2014 =
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty
                               FStar_Extraction_ML_Syntax.ml_int_ty)
                            (FStar_Extraction_ML_Syntax.MLE_Var x) in
                        let uu____2015 =
                          let uu____2017 =
                            let uu____2018 =
                              let uu____2019 =
                                FStar_Extraction_ML_Util.mlconst_of_const'
                                  p.FStar_Syntax_Syntax.p i in
                              FStar_All.pipe_left
                                (fun _0_31  ->
                                   FStar_Extraction_ML_Syntax.MLE_Const _0_31)
                                uu____2019 in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.ml_int_ty)
                              uu____2018 in
                          [uu____2017] in
                        uu____2014 :: uu____2015 in
                      (FStar_Extraction_ML_Util.prims_op_equality,
                        uu____2012) in
                    FStar_Extraction_ML_Syntax.MLE_App uu____2008 in
                  FStar_All.pipe_left
                    (FStar_Extraction_ML_Syntax.with_ty
                       FStar_Extraction_ML_Syntax.ml_bool_ty) uu____2007 in
                let uu____2021 = ok FStar_Extraction_ML_Syntax.ml_int_ty in
                (g,
                  (Some
                     ((FStar_Extraction_ML_Syntax.MLP_Var x), [when_clause])),
                  uu____2021)
            | FStar_Syntax_Syntax.Pat_constant s ->
                let t =
                  FStar_TypeChecker_TcTerm.tc_constant FStar_Range.dummyRange
                    s in
                let mlty = term_as_mlty g t in
                let uu____2033 =
                  let uu____2038 =
                    let uu____2042 =
                      let uu____2043 =
                        FStar_Extraction_ML_Util.mlconst_of_const'
                          p.FStar_Syntax_Syntax.p s in
                      FStar_Extraction_ML_Syntax.MLP_Const uu____2043 in
                    (uu____2042, []) in
                  Some uu____2038 in
                let uu____2048 = ok mlty in (g, uu____2033, uu____2048)
            | FStar_Syntax_Syntax.Pat_wild x when disjunctive_pat ->
                (g, (Some (FStar_Extraction_ML_Syntax.MLP_Wild, [])), true)
            | FStar_Syntax_Syntax.Pat_var x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort in
                let uu____2064 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp in
                (match uu____2064 with
                 | (g1,x1) ->
                     let uu____2077 = ok mlty in
                     (g1,
                       (if imp
                        then None
                        else
                          Some ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                       uu____2077))
            | FStar_Syntax_Syntax.Pat_wild x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort in
                let uu____2096 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp in
                (match uu____2096 with
                 | (g1,x1) ->
                     let uu____2109 = ok mlty in
                     (g1,
                       (if imp
                        then None
                        else
                          Some ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                       uu____2109))
            | FStar_Syntax_Syntax.Pat_dot_term uu____2126 -> (g, None, true)
            | FStar_Syntax_Syntax.Pat_cons (f,pats) ->
                let uu____2150 =
                  let uu____2153 = FStar_Extraction_ML_UEnv.lookup_fv g f in
                  match uu____2153 with
                  | FStar_Util.Inr
                      (uu____2156,{
                                    FStar_Extraction_ML_Syntax.expr =
                                      FStar_Extraction_ML_Syntax.MLE_Name n1;
                                    FStar_Extraction_ML_Syntax.mlty =
                                      uu____2158;
                                    FStar_Extraction_ML_Syntax.loc =
                                      uu____2159;_},ttys,uu____2161)
                      -> (n1, ttys)
                  | uu____2168 -> failwith "Expected a constructor" in
                (match uu____2150 with
                 | (d,tys) ->
                     let nTyVars = FStar_List.length (fst tys) in
                     let uu____2182 = FStar_Util.first_N nTyVars pats in
                     (match uu____2182 with
                      | (tysVarPats,restPats) ->
                          let f_ty_opt =
                            try
                              let mlty_args =
                                FStar_All.pipe_right tysVarPats
                                  (FStar_List.map
                                     (fun uu____2256  ->
                                        match uu____2256 with
                                        | (p1,uu____2262) ->
                                            (match p1.FStar_Syntax_Syntax.v
                                             with
                                             | FStar_Syntax_Syntax.Pat_dot_term
                                                 (uu____2267,t) ->
                                                 term_as_mlty g t
                                             | uu____2273 ->
                                                 (FStar_Extraction_ML_UEnv.debug
                                                    g
                                                    (fun uu____2275  ->
                                                       let uu____2276 =
                                                         FStar_Syntax_Print.pat_to_string
                                                           p1 in
                                                       FStar_Util.print1
                                                         "Pattern %s is not extractable"
                                                         uu____2276);
                                                  raise Un_extractable)))) in
                              let f_ty =
                                FStar_Extraction_ML_Util.subst tys mlty_args in
                              let uu____2278 =
                                FStar_Extraction_ML_Util.uncurry_mlty_fun
                                  f_ty in
                              Some uu____2278
                            with | Un_extractable  -> None in
                          let uu____2293 =
                            FStar_Util.fold_map
                              (fun g1  ->
                                 fun uu____2308  ->
                                   match uu____2308 with
                                   | (p1,imp1) ->
                                       let uu____2319 =
                                         extract_one_pat disjunctive_pat true
                                           g1 p1 None in
                                       (match uu____2319 with
                                        | (g2,p2,uu____2335) -> (g2, p2))) g
                              tysVarPats in
                          (match uu____2293 with
                           | (g1,tyMLPats) ->
                               let uu____2367 =
                                 FStar_Util.fold_map
                                   (fun uu____2393  ->
                                      fun uu____2394  ->
                                        match (uu____2393, uu____2394) with
                                        | ((g2,f_ty_opt1),(p1,imp1)) ->
                                            let uu____2443 =
                                              match f_ty_opt1 with
                                              | Some (hd1::rest,res) ->
                                                  ((Some (rest, res)),
                                                    (Some hd1))
                                              | uu____2475 -> (None, None) in
                                            (match uu____2443 with
                                             | (f_ty_opt2,expected_ty) ->
                                                 let uu____2512 =
                                                   extract_one_pat
                                                     disjunctive_pat false g2
                                                     p1 expected_ty in
                                                 (match uu____2512 with
                                                  | (g3,p2,uu____2534) ->
                                                      ((g3, f_ty_opt2), p2))))
                                   (g1, f_ty_opt) restPats in
                               (match uu____2367 with
                                | ((g2,f_ty_opt1),restMLPats) ->
                                    let uu____2595 =
                                      let uu____2601 =
                                        FStar_All.pipe_right
                                          (FStar_List.append tyMLPats
                                             restMLPats)
                                          (FStar_List.collect
                                             (fun uu___138_2626  ->
                                                match uu___138_2626 with
                                                | Some x -> [x]
                                                | uu____2648 -> [])) in
                                      FStar_All.pipe_right uu____2601
                                        FStar_List.split in
                                    (match uu____2595 with
                                     | (mlPats,when_clauses) ->
                                         let pat_ty_compat =
                                           match f_ty_opt1 with
                                           | Some ([],t) -> ok t
                                           | uu____2687 -> false in
                                         let uu____2692 =
                                           let uu____2697 =
                                             let uu____2701 =
                                               resugar_pat
                                                 f.FStar_Syntax_Syntax.fv_qual
                                                 (FStar_Extraction_ML_Syntax.MLP_CTor
                                                    (d, mlPats)) in
                                             let uu____2703 =
                                               FStar_All.pipe_right
                                                 when_clauses
                                                 FStar_List.flatten in
                                             (uu____2701, uu____2703) in
                                           Some uu____2697 in
                                         (g2, uu____2692, pat_ty_compat))))))
let extract_pat:
  FStar_Extraction_ML_UEnv.env ->
    (FStar_Syntax_Syntax.pat',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.withinfo_t ->
      FStar_Extraction_ML_Syntax.mlty ->
        (FStar_Extraction_ML_UEnv.env* (FStar_Extraction_ML_Syntax.mlpattern*
          FStar_Extraction_ML_Syntax.mlexpr option) Prims.list* Prims.bool)
  =
  fun g  ->
    fun p  ->
      fun expected_t  ->
        let extract_one_pat1 disj g1 p1 expected_t1 =
          let uu____2764 = extract_one_pat disj false g1 p1 expected_t1 in
          match uu____2764 with
          | (g2,Some (x,v1),b) -> (g2, (x, v1), b)
          | uu____2795 -> failwith "Impossible: Unable to translate pattern" in
        let mk_when_clause whens =
          match whens with
          | [] -> None
          | hd1::tl1 ->
              let uu____2820 =
                FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd1 tl1 in
              Some uu____2820 in
        match p.FStar_Syntax_Syntax.v with
        | FStar_Syntax_Syntax.Pat_disj [] ->
            failwith "Impossible: Empty disjunctive pattern"
        | FStar_Syntax_Syntax.Pat_disj (p1::pats) ->
            let uu____2846 = extract_one_pat1 true g p1 (Some expected_t) in
            (match uu____2846 with
             | (g',p2,b) ->
                 let uu____2869 =
                   FStar_Util.fold_map
                     (fun b1  ->
                        fun p3  ->
                          let uu____2881 =
                            extract_one_pat1 true g p3 (Some expected_t) in
                          match uu____2881 with
                          | (uu____2893,p4,b') -> ((b1 && b'), p4)) b pats in
                 (match uu____2869 with
                  | (b1,ps) ->
                      let ps1 = p2 :: ps in
                      let g1 = g' in
                      let uu____2931 =
                        FStar_All.pipe_right ps1
                          (FStar_List.partition
                             (fun uu___139_2959  ->
                                match uu___139_2959 with
                                | (uu____2963,uu____2964::uu____2965) -> true
                                | uu____2968 -> false)) in
                      (match uu____2931 with
                       | (ps_when,rest) ->
                           let ps2 =
                             FStar_All.pipe_right ps_when
                               (FStar_List.map
                                  (fun uu____3016  ->
                                     match uu____3016 with
                                     | (x,whens) ->
                                         let uu____3027 =
                                           mk_when_clause whens in
                                         (x, uu____3027))) in
                           let res =
                             match rest with
                             | [] -> (g1, ps2, b1)
                             | rest1 ->
                                 let uu____3057 =
                                   let uu____3062 =
                                     let uu____3066 =
                                       let uu____3067 =
                                         FStar_List.map FStar_Pervasives.fst
                                           rest1 in
                                       FStar_Extraction_ML_Syntax.MLP_Branch
                                         uu____3067 in
                                     (uu____3066, None) in
                                   uu____3062 :: ps2 in
                                 (g1, uu____3057, b1) in
                           res)))
        | uu____3081 ->
            let uu____3082 = extract_one_pat1 false g p (Some expected_t) in
            (match uu____3082 with
             | (g1,(p1,whens),b) ->
                 let when_clause = mk_when_clause whens in
                 (g1, [(p1, when_clause)], b))
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
            | FStar_Extraction_ML_Syntax.MLTY_Fun (t0,uu____3164,t1) ->
                let x = FStar_Extraction_ML_Syntax.gensym () in
                let uu____3167 =
                  let uu____3173 =
                    let uu____3178 =
                      FStar_All.pipe_left
                        (FStar_Extraction_ML_Syntax.with_ty t0)
                        (FStar_Extraction_ML_Syntax.MLE_Var x) in
                    ((x, t0), uu____3178) in
                  uu____3173 :: more_args in
                eta_args uu____3167 t1
            | FStar_Extraction_ML_Syntax.MLTY_Named (uu____3185,uu____3186)
                -> ((FStar_List.rev more_args), t)
            | uu____3198 -> failwith "Impossible: Head type is not an arrow" in
          let as_record qual1 e =
            match ((e.FStar_Extraction_ML_Syntax.expr), qual1) with
            | (FStar_Extraction_ML_Syntax.MLE_CTor (uu____3216,args),Some
               (FStar_Syntax_Syntax.Record_ctor (tyname,fields))) ->
                let path =
                  FStar_List.map FStar_Ident.text_of_id tyname.FStar_Ident.ns in
                let fields1 = record_fields fields args in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     e.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_Record (path, fields1))
            | uu____3235 -> e in
          let resugar_and_maybe_eta qual1 e =
            let uu____3248 = eta_args [] residualType in
            match uu____3248 with
            | (eargs,tres) ->
                (match eargs with
                 | [] ->
                     let uu____3276 = as_record qual1 e in
                     FStar_Extraction_ML_Util.resugar_exp uu____3276
                 | uu____3277 ->
                     let uu____3283 = FStar_List.unzip eargs in
                     (match uu____3283 with
                      | (binders,eargs1) ->
                          (match e.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_CTor (head1,args)
                               ->
                               let body =
                                 let uu____3307 =
                                   let uu____3308 =
                                     FStar_All.pipe_left
                                       (FStar_Extraction_ML_Syntax.with_ty
                                          tres)
                                       (FStar_Extraction_ML_Syntax.MLE_CTor
                                          (head1,
                                            (FStar_List.append args eargs1))) in
                                   FStar_All.pipe_left (as_record qual1)
                                     uu____3308 in
                                 FStar_All.pipe_left
                                   FStar_Extraction_ML_Util.resugar_exp
                                   uu____3307 in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    e.FStar_Extraction_ML_Syntax.mlty)
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    (binders, body))
                           | uu____3313 ->
                               failwith "Impossible: Not a constructor"))) in
          match ((mlAppExpr.FStar_Extraction_ML_Syntax.expr), qual) with
          | (uu____3315,None ) -> mlAppExpr
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____3318;
                FStar_Extraction_ML_Syntax.loc = uu____3319;_},mle::args),Some
             (FStar_Syntax_Syntax.Record_projector (constrname,f))) ->
              let f1 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append constrname.FStar_Ident.ns [f]) in
              let fn = FStar_Extraction_ML_Util.mlpath_of_lid f1 in
              let proj = FStar_Extraction_ML_Syntax.MLE_Proj (mle, fn) in
              let e =
                match args with
                | [] -> proj
                | uu____3337 ->
                    let uu____3339 =
                      let uu____3343 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj in
                      (uu____3343, args) in
                    FStar_Extraction_ML_Syntax.MLE_App uu____3339 in
              FStar_Extraction_ML_Syntax.with_ty
                mlAppExpr.FStar_Extraction_ML_Syntax.mlty e
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____3346;
                FStar_Extraction_ML_Syntax.loc = uu____3347;_},mlargs),Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____3352 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs)) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____3352
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____3355;
                FStar_Extraction_ML_Syntax.loc = uu____3356;_},mlargs),Some
             (FStar_Syntax_Syntax.Record_ctor uu____3358)) ->
              let uu____3365 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs)) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____3365
          | (FStar_Extraction_ML_Syntax.MLE_Name mlp,Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____3369 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, [])) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____3369
          | (FStar_Extraction_ML_Syntax.MLE_Name mlp,Some
             (FStar_Syntax_Syntax.Record_ctor uu____3372)) ->
              let uu____3377 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, [])) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____3377
          | uu____3379 -> mlAppExpr
let maybe_downgrade_eff:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.e_tag ->
      FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.e_tag
  =
  fun g  ->
    fun f  ->
      fun t  ->
        let uu____3392 =
          (f = FStar_Extraction_ML_Syntax.E_GHOST) &&
            (type_leq g t FStar_Extraction_ML_Syntax.ml_unit_ty) in
        if uu____3392 then FStar_Extraction_ML_Syntax.E_PURE else f
let rec term_as_mlexpr:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Extraction_ML_Syntax.mlexpr* FStar_Extraction_ML_Syntax.e_tag*
        FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun t  ->
      let uu____3433 = term_as_mlexpr' g t in
      match uu____3433 with
      | (e,tag,ty) ->
          let tag1 = maybe_downgrade_eff g tag ty in
          (FStar_Extraction_ML_UEnv.debug g
             (fun u  ->
                let uu____3446 =
                  let uu____3447 = FStar_Syntax_Print.tag_of_term t in
                  let uu____3448 = FStar_Syntax_Print.term_to_string t in
                  let uu____3449 =
                    FStar_Extraction_ML_Code.string_of_mlty
                      g.FStar_Extraction_ML_UEnv.currentModule ty in
                  FStar_Util.format4
                    "term_as_mlexpr (%s) :  %s has ML type %s and effect %s\n"
                    uu____3447 uu____3448 uu____3449
                    (FStar_Extraction_ML_Util.eff_to_string tag1) in
                FStar_Util.print_string uu____3446);
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
          let uu____3456 = check_term_as_mlexpr' g t f ty in
          match uu____3456 with
          | (e,t1) ->
              let uu____3463 = erase g e t1 f in
              (match uu____3463 with | (r,uu____3470,t2) -> (r, t2))
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
          let uu____3478 = term_as_mlexpr g e0 in
          match uu____3478 with
          | (e,tag,t) ->
              let tag1 = maybe_downgrade_eff g tag t in
              if FStar_Extraction_ML_Util.eff_leq tag1 f
              then let uu____3490 = maybe_coerce g e t ty in (uu____3490, ty)
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
           let uu____3501 =
             let uu____3502 =
               FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos in
             let uu____3503 = FStar_Syntax_Print.tag_of_term top in
             let uu____3504 = FStar_Syntax_Print.term_to_string top in
             FStar_Util.format3 "%s: term_as_mlexpr' (%s) :  %s \n"
               uu____3502 uu____3503 uu____3504 in
           FStar_Util.print_string uu____3501);
      (let t = FStar_Syntax_Subst.compress top in
       match t.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____3509 =
             let uu____3510 = FStar_Syntax_Print.tag_of_term t in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____3510 in
           failwith uu____3509
       | FStar_Syntax_Syntax.Tm_delayed uu____3514 ->
           let uu____3535 =
             let uu____3536 = FStar_Syntax_Print.tag_of_term t in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____3536 in
           failwith uu____3535
       | FStar_Syntax_Syntax.Tm_uvar uu____3540 ->
           let uu____3549 =
             let uu____3550 = FStar_Syntax_Print.tag_of_term t in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____3550 in
           failwith uu____3549
       | FStar_Syntax_Syntax.Tm_bvar uu____3554 ->
           let uu____3555 =
             let uu____3556 = FStar_Syntax_Print.tag_of_term t in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____3556 in
           failwith uu____3555
       | FStar_Syntax_Syntax.Tm_type uu____3560 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_refine uu____3561 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_arrow uu____3566 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Mutable_alloc ))
           ->
           let uu____3579 = term_as_mlexpr' g t1 in
           (match uu____3579 with
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
            | uu____3606 -> failwith "impossible")
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_monadic (m,uu____3615)) ->
           let t2 = FStar_Syntax_Subst.compress t1 in
           (match t2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) when
                FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname ->
                let uu____3638 =
                  let uu____3642 =
                    FStar_TypeChecker_Env.effect_decl_opt
                      g.FStar_Extraction_ML_UEnv.tcenv m in
                  FStar_Util.must uu____3642 in
                (match uu____3638 with
                 | (ed,qualifiers) ->
                     let uu____3657 =
                       let uu____3658 =
                         FStar_All.pipe_right qualifiers
                           (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
                       FStar_All.pipe_right uu____3658 Prims.op_Negation in
                     if uu____3657
                     then term_as_mlexpr' g t2
                     else
                       failwith
                         "This should not happen (should have been handled at Tm_abs level)")
            | uu____3667 -> term_as_mlexpr' g t2)
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____3669) -> term_as_mlexpr' g t1
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____3675) -> term_as_mlexpr' g t1
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____3681 =
             FStar_TypeChecker_TcTerm.type_of_tot_term
               g.FStar_Extraction_ML_UEnv.tcenv t in
           (match uu____3681 with
            | (uu____3688,ty,uu____3690) ->
                let ml_ty = term_as_mlty g ty in
                let uu____3692 =
                  let uu____3693 =
                    let uu____3694 =
                      FStar_Extraction_ML_Util.mlconst_of_const'
                        t.FStar_Syntax_Syntax.pos c in
                    FStar_All.pipe_left
                      (fun _0_32  ->
                         FStar_Extraction_ML_Syntax.MLE_Const _0_32)
                      uu____3694 in
                  FStar_Extraction_ML_Syntax.with_ty ml_ty uu____3693 in
                (uu____3692, FStar_Extraction_ML_Syntax.E_PURE, ml_ty))
       | FStar_Syntax_Syntax.Tm_name uu____3695 ->
           let uu____3696 = is_type g t in
           if uu____3696
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____3701 = FStar_Extraction_ML_UEnv.lookup_term g t in
              match uu____3701 with
              | (FStar_Util.Inl uu____3708,uu____3709) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | (FStar_Util.Inr (uu____3728,x,mltys,uu____3731),qual) ->
                  (match mltys with
                   | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                       ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | ([],t1) ->
                       let uu____3756 =
                         maybe_eta_data_and_project_record g qual t1 x in
                       (uu____3756, FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | uu____3757 -> err_uninst g t mltys t))
       | FStar_Syntax_Syntax.Tm_fvar uu____3761 ->
           let uu____3762 = is_type g t in
           if uu____3762
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____3767 = FStar_Extraction_ML_UEnv.lookup_term g t in
              match uu____3767 with
              | (FStar_Util.Inl uu____3774,uu____3775) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | (FStar_Util.Inr (uu____3794,x,mltys,uu____3797),qual) ->
                  (match mltys with
                   | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                       ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | ([],t1) ->
                       let uu____3822 =
                         maybe_eta_data_and_project_record g qual t1 x in
                       (uu____3822, FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | uu____3823 -> err_uninst g t mltys t))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,copt) ->
           let uu____3852 = FStar_Syntax_Subst.open_term bs body in
           (match uu____3852 with
            | (bs1,body1) ->
                let uu____3860 = binders_as_ml_binders g bs1 in
                (match uu____3860 with
                 | (ml_bs,env) ->
                     let body2 =
                       match copt with
                       | Some c ->
                           (FStar_Extraction_ML_UEnv.debug g
                              (fun uu____3890  ->
                                 match c with
                                 | FStar_Util.Inl lc ->
                                     let uu____3895 =
                                       FStar_Syntax_Print.lcomp_to_string lc in
                                     FStar_Util.print1 "Computation lc: %s\n"
                                       uu____3895
                                 | FStar_Util.Inr rc ->
                                     FStar_Util.print1 "Computation rc: %s\n"
                                       (FStar_Ident.text_of_lid (fst rc)));
                            (let uu____3904 =
                               FStar_TypeChecker_Env.is_reifiable
                                 env.FStar_Extraction_ML_UEnv.tcenv c in
                             if uu____3904
                             then
                               FStar_TypeChecker_Util.reify_body
                                 env.FStar_Extraction_ML_UEnv.tcenv body1
                             else body1))
                       | None  ->
                           (FStar_Extraction_ML_UEnv.debug g
                              (fun uu____3912  ->
                                 let uu____3913 =
                                   FStar_Syntax_Print.term_to_string body1 in
                                 FStar_Util.print1
                                   "No computation type for: %s\n" uu____3913);
                            body1) in
                     let uu____3914 = term_as_mlexpr env body2 in
                     (match uu____3914 with
                      | (ml_body,f,t1) ->
                          let uu____3924 =
                            FStar_List.fold_right
                              (fun uu____3931  ->
                                 fun uu____3932  ->
                                   match (uu____3931, uu____3932) with
                                   | ((uu____3943,targ),(f1,t2)) ->
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         (FStar_Extraction_ML_Syntax.MLTY_Fun
                                            (targ, f1, t2)))) ml_bs (f, t1) in
                          (match uu____3924 with
                           | (f1,tfun) ->
                               let uu____3956 =
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty tfun)
                                   (FStar_Extraction_ML_Syntax.MLE_Fun
                                      (ml_bs, ml_body)) in
                               (uu____3956, f1, tfun)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____3960);
              FStar_Syntax_Syntax.tk = uu____3961;
              FStar_Syntax_Syntax.pos = uu____3962;
              FStar_Syntax_Syntax.vars = uu____3963;_},uu____3964)
           -> failwith "Unreachable? Tm_app Const_reflect"
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let is_total uu___141_4006 =
             match uu___141_4006 with
             | FStar_Util.Inl l -> FStar_Syntax_Util.is_total_lcomp l
             | FStar_Util.Inr (l,flags) ->
                 (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid)
                   ||
                   (FStar_All.pipe_right flags
                      (FStar_List.existsb
                         (fun uu___140_4024  ->
                            match uu___140_4024 with
                            | FStar_Syntax_Syntax.TOTAL  -> true
                            | uu____4025 -> false))) in
           let uu____4026 =
             let uu____4029 =
               let uu____4030 = FStar_Syntax_Subst.compress head1 in
               uu____4030.FStar_Syntax_Syntax.n in
             ((head1.FStar_Syntax_Syntax.n), uu____4029) in
           (match uu____4026 with
            | (FStar_Syntax_Syntax.Tm_uvar uu____4036,uu____4037) ->
                let t1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.Iota;
                    FStar_TypeChecker_Normalize.Zeta;
                    FStar_TypeChecker_Normalize.EraseUniverses;
                    FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                    g.FStar_Extraction_ML_UEnv.tcenv t in
                term_as_mlexpr' g t1
            | (uu____4047,FStar_Syntax_Syntax.Tm_abs (bs,uu____4049,Some lc))
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
            | (uu____4078,FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_reify )) ->
                let e =
                  let uu____4080 = FStar_List.hd args in
                  FStar_TypeChecker_Util.reify_body_with_arg
                    g.FStar_Extraction_ML_UEnv.tcenv head1 uu____4080 in
                let tm =
                  let uu____4088 =
                    let uu____4089 = FStar_TypeChecker_Util.remove_reify e in
                    let uu____4090 = FStar_List.tl args in
                    FStar_Syntax_Syntax.mk_Tm_app uu____4089 uu____4090 in
                  uu____4088 None t.FStar_Syntax_Syntax.pos in
                term_as_mlexpr' g tm
            | uu____4099 ->
                let rec extract_app is_data uu____4127 uu____4128 restArgs =
                  match (uu____4127, uu____4128) with
                  | ((mlhead,mlargs_f),(f,t1)) ->
                      (match (restArgs, t1) with
                       | ([],uu____4176) ->
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
                                | uu____4190 -> false) in
                           let uu____4191 =
                             if evaluation_order_guaranteed
                             then
                               let uu____4204 =
                                 FStar_All.pipe_right
                                   (FStar_List.rev mlargs_f)
                                   (FStar_List.map FStar_Pervasives.fst) in
                               ([], uu____4204)
                             else
                               FStar_List.fold_left
                                 (fun uu____4229  ->
                                    fun uu____4230  ->
                                      match (uu____4229, uu____4230) with
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
                                             let uu____4285 =
                                               let uu____4287 =
                                                 FStar_All.pipe_left
                                                   (FStar_Extraction_ML_Syntax.with_ty
                                                      arg.FStar_Extraction_ML_Syntax.mlty)
                                                   (FStar_Extraction_ML_Syntax.MLE_Var
                                                      x) in
                                               uu____4287 :: out_args in
                                             (((x, arg) :: lbs), uu____4285)))
                                 ([], []) mlargs_f in
                           (match uu____4191 with
                            | (lbs,mlargs) ->
                                let app =
                                  let uu____4314 =
                                    FStar_All.pipe_left
                                      (FStar_Extraction_ML_Syntax.with_ty t1)
                                      (FStar_Extraction_ML_Syntax.MLE_App
                                         (mlhead, mlargs)) in
                                  FStar_All.pipe_left
                                    (maybe_eta_data_and_project_record g
                                       is_data t1) uu____4314 in
                                let l_app =
                                  FStar_List.fold_right
                                    (fun uu____4319  ->
                                       fun out  ->
                                         match uu____4319 with
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
                       | ((arg,uu____4332)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                          (formal_t,f',t2)) when
                           (is_type g arg) &&
                             (type_leq g formal_t
                                FStar_Extraction_ML_Syntax.ml_unit_ty)
                           ->
                           let uu____4350 =
                             let uu____4353 =
                               FStar_Extraction_ML_Util.join
                                 arg.FStar_Syntax_Syntax.pos f f' in
                             (uu____4353, t2) in
                           extract_app is_data
                             (mlhead,
                               ((FStar_Extraction_ML_Syntax.ml_unit,
                                  FStar_Extraction_ML_Syntax.E_PURE) ::
                               mlargs_f)) uu____4350 rest
                       | ((e0,uu____4360)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                          (tExpected,f',t2)) ->
                           let r = e0.FStar_Syntax_Syntax.pos in
                           let uu____4379 = term_as_mlexpr g e0 in
                           (match uu____4379 with
                            | (e01,f0,tInferred) ->
                                let e02 =
                                  maybe_coerce g e01 tInferred tExpected in
                                let uu____4390 =
                                  let uu____4393 =
                                    FStar_Extraction_ML_Util.join_l r
                                      [f; f'; f0] in
                                  (uu____4393, t2) in
                                extract_app is_data
                                  (mlhead, ((e02, f0) :: mlargs_f))
                                  uu____4390 rest)
                       | uu____4399 ->
                           let uu____4406 =
                             FStar_Extraction_ML_Util.udelta_unfold g t1 in
                           (match uu____4406 with
                            | Some t2 ->
                                extract_app is_data (mlhead, mlargs_f)
                                  (f, t2) restArgs
                            | None  ->
                                err_ill_typed_application g top restArgs t1)) in
                let extract_app_maybe_projector is_data mlhead uu____4442
                  args1 =
                  match uu____4442 with
                  | (f,t1) ->
                      (match is_data with
                       | Some (FStar_Syntax_Syntax.Record_projector
                           uu____4461) ->
                           let rec remove_implicits args2 f1 t2 =
                             match (args2, t2) with
                             | ((a0,Some (FStar_Syntax_Syntax.Implicit
                                 uu____4511))::args3,FStar_Extraction_ML_Syntax.MLTY_Fun
                                (uu____4513,f',t3)) ->
                                 let uu____4538 =
                                   FStar_Extraction_ML_Util.join
                                     a0.FStar_Syntax_Syntax.pos f1 f' in
                                 remove_implicits args3 uu____4538 t3
                             | uu____4539 -> (args2, f1, t2) in
                           let uu____4554 = remove_implicits args1 f t1 in
                           (match uu____4554 with
                            | (args2,f1,t2) ->
                                extract_app is_data (mlhead, []) (f1, t2)
                                  args2)
                       | uu____4587 ->
                           extract_app is_data (mlhead, []) (f, t1) args1) in
                let uu____4594 = is_type g t in
                if uu____4594
                then
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
                else
                  (let head2 = FStar_Syntax_Util.un_uinst head1 in
                   match head2.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_name uu____4603 ->
                       let uu____4604 =
                         let uu____4611 =
                           FStar_Extraction_ML_UEnv.lookup_term g head2 in
                         match uu____4611 with
                         | (FStar_Util.Inr (uu____4621,x1,x2,x3),q) ->
                             ((x1, x2, x3), q)
                         | uu____4646 -> failwith "FIXME Ty" in
                       (match uu____4604 with
                        | ((head_ml,(vars,t1),inst_ok),qual) ->
                            let has_typ_apps =
                              match args with
                              | (a,uu____4675)::uu____4676 -> is_type g a
                              | uu____4690 -> false in
                            let uu____4696 =
                              match vars with
                              | uu____4713::uu____4714 when
                                  (Prims.op_Negation has_typ_apps) && inst_ok
                                  -> (head_ml, t1, args)
                              | uu____4721 ->
                                  let n1 = FStar_List.length vars in
                                  if n1 <= (FStar_List.length args)
                                  then
                                    let uu____4741 =
                                      FStar_Util.first_N n1 args in
                                    (match uu____4741 with
                                     | (prefix1,rest) ->
                                         let prefixAsMLTypes =
                                           FStar_List.map
                                             (fun uu____4794  ->
                                                match uu____4794 with
                                                | (x,uu____4798) ->
                                                    term_as_mlty g x) prefix1 in
                                         let t2 =
                                           instantiate (vars, t1)
                                             prefixAsMLTypes in
                                         let head3 =
                                           match head_ml.FStar_Extraction_ML_Syntax.expr
                                           with
                                           | FStar_Extraction_ML_Syntax.MLE_Name
                                               uu____4801 ->
                                               let uu___145_4802 = head_ml in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (uu___145_4802.FStar_Extraction_ML_Syntax.expr);
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   = t2;
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___145_4802.FStar_Extraction_ML_Syntax.loc)
                                               }
                                           | FStar_Extraction_ML_Syntax.MLE_Var
                                               uu____4803 ->
                                               let uu___145_4804 = head_ml in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (uu___145_4804.FStar_Extraction_ML_Syntax.expr);
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   = t2;
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___145_4804.FStar_Extraction_ML_Syntax.loc)
                                               }
                                           | FStar_Extraction_ML_Syntax.MLE_App
                                               (head3,{
                                                        FStar_Extraction_ML_Syntax.expr
                                                          =
                                                          FStar_Extraction_ML_Syntax.MLE_Const
                                                          (FStar_Extraction_ML_Syntax.MLC_Unit
                                                          );
                                                        FStar_Extraction_ML_Syntax.mlty
                                                          = uu____4806;
                                                        FStar_Extraction_ML_Syntax.loc
                                                          = uu____4807;_}::[])
                                               ->
                                               FStar_All.pipe_right
                                                 (FStar_Extraction_ML_Syntax.MLE_App
                                                    ((let uu___146_4810 =
                                                        head3 in
                                                      {
                                                        FStar_Extraction_ML_Syntax.expr
                                                          =
                                                          (uu___146_4810.FStar_Extraction_ML_Syntax.expr);
                                                        FStar_Extraction_ML_Syntax.mlty
                                                          =
                                                          (FStar_Extraction_ML_Syntax.MLTY_Fun
                                                             (FStar_Extraction_ML_Syntax.ml_unit_ty,
                                                               FStar_Extraction_ML_Syntax.E_PURE,
                                                               t2));
                                                        FStar_Extraction_ML_Syntax.loc
                                                          =
                                                          (uu___146_4810.FStar_Extraction_ML_Syntax.loc)
                                                      }),
                                                      [FStar_Extraction_ML_Syntax.ml_unit]))
                                                 (FStar_Extraction_ML_Syntax.with_ty
                                                    t2)
                                           | uu____4811 ->
                                               failwith
                                                 "Impossible: Unexpected head term" in
                                         (head3, t2, rest))
                                  else err_uninst g head2 (vars, t1) top in
                            (match uu____4696 with
                             | (head_ml1,head_t,args1) ->
                                 (match args1 with
                                  | [] ->
                                      let uu____4849 =
                                        maybe_eta_data_and_project_record g
                                          qual head_t head_ml1 in
                                      (uu____4849,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        head_t)
                                  | uu____4850 ->
                                      extract_app_maybe_projector qual
                                        head_ml1
                                        (FStar_Extraction_ML_Syntax.E_PURE,
                                          head_t) args1)))
                   | FStar_Syntax_Syntax.Tm_fvar uu____4856 ->
                       let uu____4857 =
                         let uu____4864 =
                           FStar_Extraction_ML_UEnv.lookup_term g head2 in
                         match uu____4864 with
                         | (FStar_Util.Inr (uu____4874,x1,x2,x3),q) ->
                             ((x1, x2, x3), q)
                         | uu____4899 -> failwith "FIXME Ty" in
                       (match uu____4857 with
                        | ((head_ml,(vars,t1),inst_ok),qual) ->
                            let has_typ_apps =
                              match args with
                              | (a,uu____4928)::uu____4929 -> is_type g a
                              | uu____4943 -> false in
                            let uu____4949 =
                              match vars with
                              | uu____4966::uu____4967 when
                                  (Prims.op_Negation has_typ_apps) && inst_ok
                                  -> (head_ml, t1, args)
                              | uu____4974 ->
                                  let n1 = FStar_List.length vars in
                                  if n1 <= (FStar_List.length args)
                                  then
                                    let uu____4994 =
                                      FStar_Util.first_N n1 args in
                                    (match uu____4994 with
                                     | (prefix1,rest) ->
                                         let prefixAsMLTypes =
                                           FStar_List.map
                                             (fun uu____5047  ->
                                                match uu____5047 with
                                                | (x,uu____5051) ->
                                                    term_as_mlty g x) prefix1 in
                                         let t2 =
                                           instantiate (vars, t1)
                                             prefixAsMLTypes in
                                         let head3 =
                                           match head_ml.FStar_Extraction_ML_Syntax.expr
                                           with
                                           | FStar_Extraction_ML_Syntax.MLE_Name
                                               uu____5054 ->
                                               let uu___145_5055 = head_ml in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (uu___145_5055.FStar_Extraction_ML_Syntax.expr);
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   = t2;
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___145_5055.FStar_Extraction_ML_Syntax.loc)
                                               }
                                           | FStar_Extraction_ML_Syntax.MLE_Var
                                               uu____5056 ->
                                               let uu___145_5057 = head_ml in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (uu___145_5057.FStar_Extraction_ML_Syntax.expr);
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   = t2;
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___145_5057.FStar_Extraction_ML_Syntax.loc)
                                               }
                                           | FStar_Extraction_ML_Syntax.MLE_App
                                               (head3,{
                                                        FStar_Extraction_ML_Syntax.expr
                                                          =
                                                          FStar_Extraction_ML_Syntax.MLE_Const
                                                          (FStar_Extraction_ML_Syntax.MLC_Unit
                                                          );
                                                        FStar_Extraction_ML_Syntax.mlty
                                                          = uu____5059;
                                                        FStar_Extraction_ML_Syntax.loc
                                                          = uu____5060;_}::[])
                                               ->
                                               FStar_All.pipe_right
                                                 (FStar_Extraction_ML_Syntax.MLE_App
                                                    ((let uu___146_5063 =
                                                        head3 in
                                                      {
                                                        FStar_Extraction_ML_Syntax.expr
                                                          =
                                                          (uu___146_5063.FStar_Extraction_ML_Syntax.expr);
                                                        FStar_Extraction_ML_Syntax.mlty
                                                          =
                                                          (FStar_Extraction_ML_Syntax.MLTY_Fun
                                                             (FStar_Extraction_ML_Syntax.ml_unit_ty,
                                                               FStar_Extraction_ML_Syntax.E_PURE,
                                                               t2));
                                                        FStar_Extraction_ML_Syntax.loc
                                                          =
                                                          (uu___146_5063.FStar_Extraction_ML_Syntax.loc)
                                                      }),
                                                      [FStar_Extraction_ML_Syntax.ml_unit]))
                                                 (FStar_Extraction_ML_Syntax.with_ty
                                                    t2)
                                           | uu____5064 ->
                                               failwith
                                                 "Impossible: Unexpected head term" in
                                         (head3, t2, rest))
                                  else err_uninst g head2 (vars, t1) top in
                            (match uu____4949 with
                             | (head_ml1,head_t,args1) ->
                                 (match args1 with
                                  | [] ->
                                      let uu____5102 =
                                        maybe_eta_data_and_project_record g
                                          qual head_t head_ml1 in
                                      (uu____5102,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        head_t)
                                  | uu____5103 ->
                                      extract_app_maybe_projector qual
                                        head_ml1
                                        (FStar_Extraction_ML_Syntax.E_PURE,
                                          head_t) args1)))
                   | uu____5109 ->
                       let uu____5110 = term_as_mlexpr g head2 in
                       (match uu____5110 with
                        | (head3,f,t1) ->
                            extract_app_maybe_projector None head3 (f, t1)
                              args)))
       | FStar_Syntax_Syntax.Tm_ascribed (e0,(tc,uu____5122),f) ->
           let t1 =
             match tc with
             | FStar_Util.Inl t1 -> term_as_mlty g t1
             | FStar_Util.Inr c ->
                 term_as_mlty g (FStar_Syntax_Util.comp_result c) in
           let f1 =
             match f with
             | None  -> failwith "Ascription node with an empty effect label"
             | Some l -> effect_as_etag g l in
           let uu____5176 = check_term_as_mlexpr g e0 f1 t1 in
           (match uu____5176 with | (e,t2) -> (e, f1, t2))
       | FStar_Syntax_Syntax.Tm_let ((is_rec,lbs),e') ->
           let top_level = FStar_Syntax_Syntax.is_top_level lbs in
           let uu____5197 =
             if is_rec
             then FStar_Syntax_Subst.open_let_rec lbs e'
             else
               (let uu____5205 = FStar_Syntax_Syntax.is_top_level lbs in
                if uu____5205
                then (lbs, e')
                else
                  (let lb = FStar_List.hd lbs in
                   let x =
                     let uu____5215 =
                       FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                     FStar_Syntax_Syntax.freshen_bv uu____5215 in
                   let lb1 =
                     let uu___147_5217 = lb in
                     {
                       FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                       FStar_Syntax_Syntax.lbunivs =
                         (uu___147_5217.FStar_Syntax_Syntax.lbunivs);
                       FStar_Syntax_Syntax.lbtyp =
                         (uu___147_5217.FStar_Syntax_Syntax.lbtyp);
                       FStar_Syntax_Syntax.lbeff =
                         (uu___147_5217.FStar_Syntax_Syntax.lbeff);
                       FStar_Syntax_Syntax.lbdef =
                         (uu___147_5217.FStar_Syntax_Syntax.lbdef)
                     } in
                   let e'1 =
                     FStar_Syntax_Subst.subst
                       [FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x)] e' in
                   ([lb1], e'1))) in
           (match uu____5197 with
            | (lbs1,e'1) ->
                let lbs2 =
                  if top_level
                  then
                    FStar_All.pipe_right lbs1
                      (FStar_List.map
                         (fun lb  ->
                            let tcenv =
                              let uu____5234 =
                                FStar_Ident.lid_of_path
                                  (FStar_List.append
                                     (fst
                                        g.FStar_Extraction_ML_UEnv.currentModule)
                                     [snd
                                        g.FStar_Extraction_ML_UEnv.currentModule])
                                  FStar_Range.dummyRange in
                              FStar_TypeChecker_Env.set_current_module
                                g.FStar_Extraction_ML_UEnv.tcenv uu____5234 in
                            FStar_Extraction_ML_UEnv.debug g
                              (fun uu____5238  ->
                                 FStar_Options.set_option "debug_level"
                                   (FStar_Options.List
                                      [FStar_Options.String "Norm";
                                      FStar_Options.String "Extraction"]));
                            (let lbdef =
                               let uu____5242 = FStar_Options.ml_ish () in
                               if uu____5242
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
                             let uu___148_5246 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___148_5246.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___148_5246.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___148_5246.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___148_5246.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef
                             })))
                  else lbs1 in
                let maybe_generalize uu____5260 =
                  match uu____5260 with
                  | { FStar_Syntax_Syntax.lbname = lbname_;
                      FStar_Syntax_Syntax.lbunivs = uu____5271;
                      FStar_Syntax_Syntax.lbtyp = t1;
                      FStar_Syntax_Syntax.lbeff = lbeff;
                      FStar_Syntax_Syntax.lbdef = e;_} ->
                      let f_e = effect_as_etag g lbeff in
                      let t2 = FStar_Syntax_Subst.compress t1 in
                      (match t2.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                           let uu____5314 = FStar_List.hd bs in
                           FStar_All.pipe_right uu____5314 (is_type_binder g)
                           ->
                           let uu____5321 = FStar_Syntax_Subst.open_comp bs c in
                           (match uu____5321 with
                            | (bs1,c1) ->
                                let uu____5335 =
                                  let uu____5340 =
                                    FStar_Util.prefix_until
                                      (fun x  ->
                                         let uu____5358 = is_type_binder g x in
                                         Prims.op_Negation uu____5358) bs1 in
                                  match uu____5340 with
                                  | None  ->
                                      (bs1,
                                        (FStar_Syntax_Util.comp_result c1))
                                  | Some (bs2,b,rest) ->
                                      let uu____5406 =
                                        FStar_Syntax_Util.arrow (b :: rest)
                                          c1 in
                                      (bs2, uu____5406) in
                                (match uu____5335 with
                                 | (tbinders,tbody) ->
                                     let n_tbinders =
                                       FStar_List.length tbinders in
                                     let e1 =
                                       let uu____5436 = normalize_abs e in
                                       FStar_All.pipe_right uu____5436
                                         FStar_Syntax_Util.unmeta in
                                     (match e1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Tm_abs
                                          (bs2,body,copt) ->
                                          let uu____5471 =
                                            FStar_Syntax_Subst.open_term bs2
                                              body in
                                          (match uu____5471 with
                                           | (bs3,body1) ->
                                               if
                                                 n_tbinders <=
                                                   (FStar_List.length bs3)
                                               then
                                                 let uu____5501 =
                                                   FStar_Util.first_N
                                                     n_tbinders bs3 in
                                                 (match uu____5501 with
                                                  | (targs,rest_args) ->
                                                      let expected_source_ty
                                                        =
                                                        let s =
                                                          FStar_List.map2
                                                            (fun uu____5544 
                                                               ->
                                                               fun uu____5545
                                                                  ->
                                                                 match 
                                                                   (uu____5544,
                                                                    uu____5545)
                                                                 with
                                                                 | ((x,uu____5555),
                                                                    (y,uu____5557))
                                                                    ->
                                                                    let uu____5562
                                                                    =
                                                                    let uu____5567
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    y in
                                                                    (x,
                                                                    uu____5567) in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____5562)
                                                            tbinders targs in
                                                        FStar_Syntax_Subst.subst
                                                          s tbody in
                                                      let env =
                                                        FStar_List.fold_left
                                                          (fun env  ->
                                                             fun uu____5572 
                                                               ->
                                                               match uu____5572
                                                               with
                                                               | (a,uu____5576)
                                                                   ->
                                                                   FStar_Extraction_ML_UEnv.extend_ty
                                                                    env a
                                                                    None) g
                                                          targs in
                                                      let expected_t =
                                                        term_as_mlty env
                                                          expected_source_ty in
                                                      let polytype =
                                                        let uu____5584 =
                                                          FStar_All.pipe_right
                                                            targs
                                                            (FStar_List.map
                                                               (fun
                                                                  uu____5598 
                                                                  ->
                                                                  match uu____5598
                                                                  with
                                                                  | (x,uu____5604)
                                                                    ->
                                                                    FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                                    x)) in
                                                        (uu____5584,
                                                          expected_t) in
                                                      let add_unit =
                                                        match rest_args with
                                                        | [] ->
                                                            let uu____5611 =
                                                              is_fstar_value
                                                                body1 in
                                                            Prims.op_Negation
                                                              uu____5611
                                                        | uu____5612 -> false in
                                                      let rest_args1 =
                                                        if add_unit
                                                        then unit_binder ::
                                                          rest_args
                                                        else rest_args in
                                                      let body2 =
                                                        match rest_args1 with
                                                        | [] -> body1
                                                        | uu____5621 ->
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
                                          uu____5665 ->
                                          let env =
                                            FStar_List.fold_left
                                              (fun env  ->
                                                 fun uu____5674  ->
                                                   match uu____5674 with
                                                   | (a,uu____5678) ->
                                                       FStar_Extraction_ML_UEnv.extend_ty
                                                         env a None) g
                                              tbinders in
                                          let expected_t =
                                            term_as_mlty env tbody in
                                          let polytype =
                                            let uu____5686 =
                                              FStar_All.pipe_right tbinders
                                                (FStar_List.map
                                                   (fun uu____5697  ->
                                                      match uu____5697 with
                                                      | (x,uu____5703) ->
                                                          FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                            x)) in
                                            (uu____5686, expected_t) in
                                          let args =
                                            FStar_All.pipe_right tbinders
                                              (FStar_List.map
                                                 (fun uu____5712  ->
                                                    match uu____5712 with
                                                    | (bv,uu____5716) ->
                                                        let uu____5717 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            bv in
                                                        FStar_All.pipe_right
                                                          uu____5717
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
                                          uu____5751 ->
                                          let env =
                                            FStar_List.fold_left
                                              (fun env  ->
                                                 fun uu____5756  ->
                                                   match uu____5756 with
                                                   | (a,uu____5760) ->
                                                       FStar_Extraction_ML_UEnv.extend_ty
                                                         env a None) g
                                              tbinders in
                                          let expected_t =
                                            term_as_mlty env tbody in
                                          let polytype =
                                            let uu____5768 =
                                              FStar_All.pipe_right tbinders
                                                (FStar_List.map
                                                   (fun uu____5779  ->
                                                      match uu____5779 with
                                                      | (x,uu____5785) ->
                                                          FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                            x)) in
                                            (uu____5768, expected_t) in
                                          let args =
                                            FStar_All.pipe_right tbinders
                                              (FStar_List.map
                                                 (fun uu____5794  ->
                                                    match uu____5794 with
                                                    | (bv,uu____5798) ->
                                                        let uu____5799 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            bv in
                                                        FStar_All.pipe_right
                                                          uu____5799
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
                                          uu____5833 ->
                                          let env =
                                            FStar_List.fold_left
                                              (fun env  ->
                                                 fun uu____5838  ->
                                                   match uu____5838 with
                                                   | (a,uu____5842) ->
                                                       FStar_Extraction_ML_UEnv.extend_ty
                                                         env a None) g
                                              tbinders in
                                          let expected_t =
                                            term_as_mlty env tbody in
                                          let polytype =
                                            let uu____5850 =
                                              FStar_All.pipe_right tbinders
                                                (FStar_List.map
                                                   (fun uu____5861  ->
                                                      match uu____5861 with
                                                      | (x,uu____5867) ->
                                                          FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                            x)) in
                                            (uu____5850, expected_t) in
                                          let args =
                                            FStar_All.pipe_right tbinders
                                              (FStar_List.map
                                                 (fun uu____5876  ->
                                                    match uu____5876 with
                                                    | (bv,uu____5880) ->
                                                        let uu____5881 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            bv in
                                                        FStar_All.pipe_right
                                                          uu____5881
                                                          FStar_Syntax_Syntax.as_arg)) in
                                          let e2 =
                                            FStar_Syntax_Syntax.mk
                                              (FStar_Syntax_Syntax.Tm_app
                                                 (e1, args)) None
                                              e1.FStar_Syntax_Syntax.pos in
                                          (lbname_, f_e,
                                            (t2, (tbinders, polytype)),
                                            false, e2)
                                      | uu____5915 ->
                                          err_value_restriction e1)))
                       | uu____5925 ->
                           let expected_t = term_as_mlty g t2 in
                           (lbname_, f_e, (t2, ([], ([], expected_t))),
                             false, e)) in
                let check_lb env uu____5982 =
                  match uu____5982 with
                  | (nm,(lbname,f,(t1,(targs,polytype)),add_unit,e)) ->
                      let env1 =
                        FStar_List.fold_left
                          (fun env1  ->
                             fun uu____6053  ->
                               match uu____6053 with
                               | (a,uu____6057) ->
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
                      let uu____6060 =
                        check_term_as_mlexpr env1 e f expected_t in
                      (match uu____6060 with
                       | (e1,uu____6066) ->
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
                let uu____6101 =
                  FStar_List.fold_right
                    (fun lb  ->
                       fun uu____6140  ->
                         match uu____6140 with
                         | (env,lbs4) ->
                             let uu____6204 = lb in
                             (match uu____6204 with
                              | (lbname,uu____6229,(t1,(uu____6231,polytype)),add_unit,uu____6234)
                                  ->
                                  let uu____6241 =
                                    FStar_Extraction_ML_UEnv.extend_lb env
                                      lbname t1 polytype add_unit true in
                                  (match uu____6241 with
                                   | (env1,nm) -> (env1, ((nm, lb) :: lbs4)))))
                    lbs3 (g, []) in
                (match uu____6101 with
                 | (env_body,lbs4) ->
                     let env_def = if is_rec then env_body else g in
                     let lbs5 =
                       FStar_All.pipe_right lbs4
                         (FStar_List.map (check_lb env_def)) in
                     let e'_rng = e'1.FStar_Syntax_Syntax.pos in
                     let uu____6384 = term_as_mlexpr env_body e'1 in
                     (match uu____6384 with
                      | (e'2,f',t') ->
                          let f =
                            let uu____6395 =
                              let uu____6397 =
                                FStar_List.map FStar_Pervasives.fst lbs5 in
                              f' :: uu____6397 in
                            FStar_Extraction_ML_Util.join_l e'_rng uu____6395 in
                          let is_rec1 =
                            if is_rec = true
                            then FStar_Extraction_ML_Syntax.Rec
                            else FStar_Extraction_ML_Syntax.NonRec in
                          let uu____6403 =
                            let uu____6404 =
                              let uu____6405 =
                                let uu____6406 =
                                  FStar_List.map FStar_Pervasives.snd lbs5 in
                                (is_rec1, [], uu____6406) in
                              mk_MLE_Let top_level uu____6405 e'2 in
                            let uu____6412 =
                              FStar_Extraction_ML_Util.mlloc_of_range
                                t.FStar_Syntax_Syntax.pos in
                            FStar_Extraction_ML_Syntax.with_ty_loc t'
                              uu____6404 uu____6412 in
                          (uu____6403, f, t'))))
       | FStar_Syntax_Syntax.Tm_match (scrutinee,pats) ->
           let uu____6441 = term_as_mlexpr g scrutinee in
           (match uu____6441 with
            | (e,f_e,t_e) ->
                let uu____6451 = check_pats_for_ite pats in
                (match uu____6451 with
                 | (b,then_e,else_e) ->
                     let no_lift x t1 = x in
                     if b
                     then
                       (match (then_e, else_e) with
                        | (Some then_e1,Some else_e1) ->
                            let uu____6486 = term_as_mlexpr g then_e1 in
                            (match uu____6486 with
                             | (then_mle,f_then,t_then) ->
                                 let uu____6496 = term_as_mlexpr g else_e1 in
                                 (match uu____6496 with
                                  | (else_mle,f_else,t_else) ->
                                      let uu____6506 =
                                        let uu____6513 =
                                          type_leq g t_then t_else in
                                        if uu____6513
                                        then (t_else, no_lift)
                                        else
                                          (let uu____6525 =
                                             type_leq g t_else t_then in
                                           if uu____6525
                                           then (t_then, no_lift)
                                           else
                                             (FStar_Extraction_ML_Syntax.MLTY_Top,
                                               FStar_Extraction_ML_Syntax.apply_obj_repr)) in
                                      (match uu____6506 with
                                       | (t_branch,maybe_lift1) ->
                                           let uu____6554 =
                                             let uu____6555 =
                                               let uu____6556 =
                                                 let uu____6561 =
                                                   maybe_lift1 then_mle
                                                     t_then in
                                                 let uu____6562 =
                                                   let uu____6564 =
                                                     maybe_lift1 else_mle
                                                       t_else in
                                                   Some uu____6564 in
                                                 (e, uu____6561, uu____6562) in
                                               FStar_Extraction_ML_Syntax.MLE_If
                                                 uu____6556 in
                                             FStar_All.pipe_left
                                               (FStar_Extraction_ML_Syntax.with_ty
                                                  t_branch) uu____6555 in
                                           let uu____6566 =
                                             FStar_Extraction_ML_Util.join
                                               then_e1.FStar_Syntax_Syntax.pos
                                               f_then f_else in
                                           (uu____6554, uu____6566, t_branch))))
                        | uu____6567 ->
                            failwith
                              "ITE pats matched but then and else expressions not found?")
                     else
                       (let uu____6576 =
                          FStar_All.pipe_right pats
                            (FStar_Util.fold_map
                               (fun compat  ->
                                  fun br  ->
                                    let uu____6626 =
                                      FStar_Syntax_Subst.open_branch br in
                                    match uu____6626 with
                                    | (pat,when_opt,branch1) ->
                                        let uu____6656 =
                                          extract_pat g pat t_e in
                                        (match uu____6656 with
                                         | (env,p,pat_t_compat) ->
                                             let uu____6687 =
                                               match when_opt with
                                               | None  ->
                                                   (None,
                                                     FStar_Extraction_ML_Syntax.E_PURE)
                                               | Some w ->
                                                   let uu____6702 =
                                                     term_as_mlexpr env w in
                                                   (match uu____6702 with
                                                    | (w1,f_w,t_w) ->
                                                        let w2 =
                                                          maybe_coerce env w1
                                                            t_w
                                                            FStar_Extraction_ML_Syntax.ml_bool_ty in
                                                        ((Some w2), f_w)) in
                                             (match uu____6687 with
                                              | (when_opt1,f_when) ->
                                                  let uu____6730 =
                                                    term_as_mlexpr env
                                                      branch1 in
                                                  (match uu____6730 with
                                                   | (mlbranch,f_branch,t_branch)
                                                       ->
                                                       let uu____6749 =
                                                         FStar_All.pipe_right
                                                           p
                                                           (FStar_List.map
                                                              (fun uu____6786
                                                                  ->
                                                                 match uu____6786
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
                                                         uu____6749))))) true) in
                        match uu____6576 with
                        | (pat_t_compat,mlbranches) ->
                            let mlbranches1 = FStar_List.flatten mlbranches in
                            let e1 =
                              if pat_t_compat
                              then e
                              else
                                (FStar_Extraction_ML_UEnv.debug g
                                   (fun uu____6872  ->
                                      let uu____6873 =
                                        FStar_Extraction_ML_Code.string_of_mlexpr
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          e in
                                      let uu____6874 =
                                        FStar_Extraction_ML_Code.string_of_mlty
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          t_e in
                                      FStar_Util.print2
                                        "Coercing scrutinee %s from type %s because pattern type is incompatible\n"
                                        uu____6873 uu____6874);
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty t_e)
                                   (FStar_Extraction_ML_Syntax.MLE_Coerce
                                      (e, t_e,
                                        FStar_Extraction_ML_Syntax.MLTY_Top))) in
                            (match mlbranches1 with
                             | [] ->
                                 let uu____6887 =
                                   let uu____6892 =
                                     let uu____6901 =
                                       FStar_Syntax_Syntax.lid_as_fv
                                         FStar_Syntax_Const.failwith_lid
                                         FStar_Syntax_Syntax.Delta_constant
                                         None in
                                     FStar_Extraction_ML_UEnv.lookup_fv g
                                       uu____6901 in
                                   FStar_All.pipe_left FStar_Util.right
                                     uu____6892 in
                                 (match uu____6887 with
                                  | (uu____6923,fw,uu____6925,uu____6926) ->
                                      let uu____6927 =
                                        let uu____6928 =
                                          let uu____6929 =
                                            let uu____6933 =
                                              let uu____6935 =
                                                FStar_All.pipe_left
                                                  (FStar_Extraction_ML_Syntax.with_ty
                                                     FStar_Extraction_ML_Syntax.ml_string_ty)
                                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                                     (FStar_Extraction_ML_Syntax.MLC_String
                                                        "unreachable")) in
                                              [uu____6935] in
                                            (fw, uu____6933) in
                                          FStar_Extraction_ML_Syntax.MLE_App
                                            uu____6929 in
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             FStar_Extraction_ML_Syntax.ml_unit_ty)
                                          uu____6928 in
                                      (uu____6927,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        FStar_Extraction_ML_Syntax.ml_unit_ty))
                             | (uu____6937,uu____6938,(uu____6939,f_first,t_first))::rest
                                 ->
                                 let uu____6971 =
                                   FStar_List.fold_left
                                     (fun uu____6987  ->
                                        fun uu____6988  ->
                                          match (uu____6987, uu____6988) with
                                          | ((topt,f),(uu____7018,uu____7019,
                                                       (uu____7020,f_branch,t_branch)))
                                              ->
                                              let f1 =
                                                FStar_Extraction_ML_Util.join
                                                  top.FStar_Syntax_Syntax.pos
                                                  f f_branch in
                                              let topt1 =
                                                match topt with
                                                | None  -> None
                                                | Some t1 ->
                                                    let uu____7051 =
                                                      type_leq g t1 t_branch in
                                                    if uu____7051
                                                    then Some t_branch
                                                    else
                                                      (let uu____7054 =
                                                         type_leq g t_branch
                                                           t1 in
                                                       if uu____7054
                                                       then Some t1
                                                       else None) in
                                              (topt1, f1))
                                     ((Some t_first), f_first) rest in
                                 (match uu____6971 with
                                  | (topt,f_match) ->
                                      let mlbranches2 =
                                        FStar_All.pipe_right mlbranches1
                                          (FStar_List.map
                                             (fun uu____7100  ->
                                                match uu____7100 with
                                                | (p,(wopt,uu____7116),
                                                   (b1,uu____7118,t1)) ->
                                                    let b2 =
                                                      match topt with
                                                      | None  ->
                                                          FStar_Extraction_ML_Syntax.apply_obj_repr
                                                            b1 t1
                                                      | Some uu____7129 -> b1 in
                                                    (p, wopt, b2))) in
                                      let t_match =
                                        match topt with
                                        | None  ->
                                            FStar_Extraction_ML_Syntax.MLTY_Top
                                        | Some t1 -> t1 in
                                      let uu____7133 =
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             t_match)
                                          (FStar_Extraction_ML_Syntax.MLE_Match
                                             (e1, mlbranches2)) in
                                      (uu____7133, f_match, t_match)))))))
let fresh: Prims.string -> (Prims.string* Prims.int) =
  let c = FStar_Util.mk_ref (Prims.parse_int "0") in
  fun x  ->
    FStar_Util.incr c; (let uu____7151 = FStar_ST.read c in (x, uu____7151))
let ind_discriminator_body:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlmodule1
  =
  fun env  ->
    fun discName  ->
      fun constrName  ->
        let uu____7163 =
          let uu____7166 =
            FStar_TypeChecker_Env.lookup_lid
              env.FStar_Extraction_ML_UEnv.tcenv discName in
          FStar_All.pipe_left FStar_Pervasives.fst uu____7166 in
        match uu____7163 with
        | (uu____7179,fstar_disc_type) ->
            let wildcards =
              let uu____7187 =
                let uu____7188 = FStar_Syntax_Subst.compress fstar_disc_type in
                uu____7188.FStar_Syntax_Syntax.n in
              match uu____7187 with
              | FStar_Syntax_Syntax.Tm_arrow (binders,uu____7197) ->
                  let uu____7208 =
                    FStar_All.pipe_right binders
                      (FStar_List.filter
                         (fun uu___142_7223  ->
                            match uu___142_7223 with
                            | (uu____7227,Some (FStar_Syntax_Syntax.Implicit
                               uu____7228)) -> true
                            | uu____7230 -> false)) in
                  FStar_All.pipe_right uu____7208
                    (FStar_List.map
                       (fun uu____7250  ->
                          let uu____7254 = fresh "_" in
                          (uu____7254, FStar_Extraction_ML_Syntax.MLTY_Top)))
              | uu____7259 -> failwith "Discriminator must be a function" in
            let mlid = fresh "_discr_" in
            let targ = FStar_Extraction_ML_Syntax.MLTY_Top in
            let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top in
            let discrBody =
              let uu____7271 =
                let uu____7272 =
                  let uu____7278 =
                    let uu____7279 =
                      let uu____7280 =
                        let uu____7288 =
                          let uu____7289 =
                            let uu____7290 =
                              let uu____7291 =
                                FStar_Extraction_ML_Syntax.idsym mlid in
                              ([], uu____7291) in
                            FStar_Extraction_ML_Syntax.MLE_Name uu____7290 in
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty targ)
                            uu____7289 in
                        let uu____7293 =
                          let uu____7299 =
                            let uu____7304 =
                              let uu____7305 =
                                let uu____7309 =
                                  FStar_Extraction_ML_Syntax.mlpath_of_lident
                                    constrName in
                                (uu____7309,
                                  [FStar_Extraction_ML_Syntax.MLP_Wild]) in
                              FStar_Extraction_ML_Syntax.MLP_CTor uu____7305 in
                            let uu____7311 =
                              FStar_All.pipe_left
                                (FStar_Extraction_ML_Syntax.with_ty
                                   FStar_Extraction_ML_Syntax.ml_bool_ty)
                                (FStar_Extraction_ML_Syntax.MLE_Const
                                   (FStar_Extraction_ML_Syntax.MLC_Bool true)) in
                            (uu____7304, None, uu____7311) in
                          let uu____7313 =
                            let uu____7319 =
                              let uu____7324 =
                                FStar_All.pipe_left
                                  (FStar_Extraction_ML_Syntax.with_ty
                                     FStar_Extraction_ML_Syntax.ml_bool_ty)
                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                     (FStar_Extraction_ML_Syntax.MLC_Bool
                                        false)) in
                              (FStar_Extraction_ML_Syntax.MLP_Wild, None,
                                uu____7324) in
                            [uu____7319] in
                          uu____7299 :: uu____7313 in
                        (uu____7288, uu____7293) in
                      FStar_Extraction_ML_Syntax.MLE_Match uu____7280 in
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.ml_bool_ty) uu____7279 in
                  ((FStar_List.append wildcards [(mlid, targ)]), uu____7278) in
                FStar_Extraction_ML_Syntax.MLE_Fun uu____7272 in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty disc_ty) uu____7271 in
            let uu____7362 =
              let uu____7363 =
                let uu____7365 =
                  let uu____7366 =
                    FStar_Extraction_ML_UEnv.convIdent
                      discName.FStar_Ident.ident in
                  {
                    FStar_Extraction_ML_Syntax.mllb_name = uu____7366;
                    FStar_Extraction_ML_Syntax.mllb_tysc = None;
                    FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                    FStar_Extraction_ML_Syntax.mllb_def = discrBody;
                    FStar_Extraction_ML_Syntax.print_typ = false
                  } in
                [uu____7365] in
              (FStar_Extraction_ML_Syntax.NonRec, [], uu____7363) in
            FStar_Extraction_ML_Syntax.MLM_Let uu____7362