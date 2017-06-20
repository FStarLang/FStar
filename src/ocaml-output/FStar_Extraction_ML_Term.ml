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
  (let uu____80 =
     let uu____81 = FStar_Range.string_of_range r in
     FStar_Util.format2 "%s: %s\n" uu____81 msg in
   FStar_All.pipe_left FStar_Util.print_string uu____80);
  failwith msg
let err_uninst env t uu____109 app =
  match uu____109 with
  | (vars,ty) ->
      let uu____124 =
        let uu____125 = FStar_Syntax_Print.term_to_string t in
        let uu____126 =
          let uu____127 =
            FStar_All.pipe_right vars (FStar_List.map FStar_Pervasives.fst) in
          FStar_All.pipe_right uu____127 (FStar_String.concat ", ") in
        let uu____136 =
          FStar_Extraction_ML_Code.string_of_mlty
            env.FStar_Extraction_ML_UEnv.currentModule ty in
        let uu____137 = FStar_Syntax_Print.term_to_string app in
        FStar_Util.format4
          "Variable %s has a polymorphic type (forall %s. %s); expected it to be fully instantiated, but got %s"
          uu____125 uu____126 uu____136 uu____137 in
      fail t.FStar_Syntax_Syntax.pos uu____124
let err_ill_typed_application env t args ty =
  let uu____168 =
    let uu____169 = FStar_Syntax_Print.term_to_string t in
    let uu____170 =
      let uu____171 =
        FStar_All.pipe_right args
          (FStar_List.map
             (fun uu____182  ->
                match uu____182 with
                | (x,uu____186) -> FStar_Syntax_Print.term_to_string x)) in
      FStar_All.pipe_right uu____171 (FStar_String.concat " ") in
    let uu____188 =
      FStar_Extraction_ML_Code.string_of_mlty
        env.FStar_Extraction_ML_UEnv.currentModule ty in
    FStar_Util.format3
      "Ill-typed application: application is %s \n remaining args are %s\nml type of head is %s\n"
      uu____169 uu____170 uu____188 in
  fail t.FStar_Syntax_Syntax.pos uu____168
let err_value_restriction t =
  let uu____200 =
    let uu____201 = FStar_Syntax_Print.tag_of_term t in
    let uu____202 = FStar_Syntax_Print.term_to_string t in
    FStar_Util.format2
      "Refusing to generalize because of the value restriction: (%s) %s"
      uu____201 uu____202 in
  fail t.FStar_Syntax_Syntax.pos uu____200
let err_unexpected_eff t f0 f1 =
  let uu____224 =
    let uu____225 = FStar_Syntax_Print.term_to_string t in
    FStar_Util.format3 "for expression %s, Expected effect %s; got effect %s"
      uu____225 (FStar_Extraction_ML_Util.eff_to_string f0)
      (FStar_Extraction_ML_Util.eff_to_string f1) in
  fail t.FStar_Syntax_Syntax.pos uu____224
let effect_as_etag:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Ident.lident -> FStar_Extraction_ML_Syntax.e_tag
  =
  let cache = FStar_Util.smap_create (Prims.parse_int "20") in
  let rec delta_norm_eff g l =
    let uu____239 = FStar_Util.smap_try_find cache l.FStar_Ident.str in
    match uu____239 with
    | Some l1 -> l1
    | None  ->
        let res =
          let uu____243 =
            FStar_TypeChecker_Env.lookup_effect_abbrev
              g.FStar_Extraction_ML_UEnv.tcenv [FStar_Syntax_Syntax.U_zero] l in
          match uu____243 with
          | None  -> l
          | Some (uu____249,c) ->
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
               let uu____271 =
                 FStar_All.pipe_right qualifiers
                   (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
               if uu____271
               then FStar_Extraction_ML_Syntax.E_PURE
               else FStar_Extraction_ML_Syntax.E_IMPURE
           | None  -> FStar_Extraction_ML_Syntax.E_IMPURE)
let rec is_arity:
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t in
      let uu____284 =
        let uu____285 = FStar_Syntax_Subst.compress t1 in
        uu____285.FStar_Syntax_Syntax.n in
      match uu____284 with
      | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____288 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_ascribed uu____309 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_meta uu____327 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_uvar uu____332 -> false
      | FStar_Syntax_Syntax.Tm_constant uu____343 -> false
      | FStar_Syntax_Syntax.Tm_name uu____344 -> false
      | FStar_Syntax_Syntax.Tm_bvar uu____345 -> false
      | FStar_Syntax_Syntax.Tm_type uu____346 -> true
      | FStar_Syntax_Syntax.Tm_arrow (uu____347,c) ->
          is_arity env (FStar_Syntax_Util.comp_result c)
      | FStar_Syntax_Syntax.Tm_fvar uu____359 ->
          let t2 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Normalize.AllowUnboundUniverses;
              FStar_TypeChecker_Normalize.EraseUniverses;
              FStar_TypeChecker_Normalize.UnfoldUntil
                FStar_Syntax_Syntax.Delta_constant]
              env.FStar_Extraction_ML_UEnv.tcenv t1 in
          let uu____361 =
            let uu____362 = FStar_Syntax_Subst.compress t2 in
            uu____362.FStar_Syntax_Syntax.n in
          (match uu____361 with
           | FStar_Syntax_Syntax.Tm_fvar uu____365 -> false
           | uu____366 -> is_arity env t2)
      | FStar_Syntax_Syntax.Tm_app uu____367 ->
          let uu____377 = FStar_Syntax_Util.head_and_args t1 in
          (match uu____377 with | (head1,uu____388) -> is_arity env head1)
      | FStar_Syntax_Syntax.Tm_uinst (head1,uu____404) -> is_arity env head1
      | FStar_Syntax_Syntax.Tm_refine (x,uu____410) ->
          is_arity env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_abs (uu____415,body,uu____417) ->
          is_arity env body
      | FStar_Syntax_Syntax.Tm_let (uu____440,body) -> is_arity env body
      | FStar_Syntax_Syntax.Tm_match (uu____452,branches) ->
          (match branches with
           | (uu____478,uu____479,e)::uu____481 -> is_arity env e
           | uu____513 -> false)
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
            (let uu____575 =
               FStar_TypeChecker_Env.lookup_lid
                 env.FStar_Extraction_ML_UEnv.tcenv
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
             match uu____575 with
             | ((us,t2),uu____582) ->
                 (FStar_Extraction_ML_UEnv.debug env
                    (fun uu____590  ->
                       let uu____591 = FStar_Syntax_Print.fv_to_string fv in
                       let uu____592 =
                         let uu____593 =
                           FStar_List.map FStar_Syntax_Print.univ_to_string
                             us in
                         FStar_All.pipe_right uu____593
                           (FStar_String.concat ", ") in
                       let uu____596 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.print3 "Looked up type of %s; got <%s>.%s"
                         uu____591 uu____592 uu____596);
                  is_arity env t2))
      | FStar_Syntax_Syntax.Tm_uvar (uu____597,t2) -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_bvar
          { FStar_Syntax_Syntax.ppname = uu____615;
            FStar_Syntax_Syntax.index = uu____616;
            FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_name
          { FStar_Syntax_Syntax.ppname = uu____620;
            FStar_Syntax_Syntax.index = uu____621;
            FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____626,uu____627) ->
          is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____657) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____664) ->
          let uu____687 = FStar_Syntax_Subst.open_term bs body in
          (match uu____687 with | (uu____690,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
          let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
          let uu____703 =
            let uu____706 =
              let uu____707 = FStar_Syntax_Syntax.mk_binder x in [uu____707] in
            FStar_Syntax_Subst.open_term uu____706 body in
          (match uu____703 with | (uu____708,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_let ((uu____710,lbs),body) ->
          let uu____722 = FStar_Syntax_Subst.open_let_rec lbs body in
          (match uu____722 with | (uu____726,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_match (uu____730,branches) ->
          (match branches with
           | b::uu____757 ->
               let uu____786 = FStar_Syntax_Subst.open_branch b in
               (match uu____786 with
                | (uu____787,uu____788,e) -> is_type_aux env e)
           | uu____802 -> false)
      | FStar_Syntax_Syntax.Tm_meta (t2,uu____814) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_app (head1,uu____820) -> is_type_aux env head1
let is_type:
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      FStar_Extraction_ML_UEnv.debug env
        (fun uu____845  ->
           let uu____846 = FStar_Syntax_Print.tag_of_term t in
           let uu____847 = FStar_Syntax_Print.term_to_string t in
           FStar_Util.print2 "checking is_type (%s) %s\n" uu____846 uu____847);
      (let b = is_type_aux env t in
       FStar_Extraction_ML_UEnv.debug env
         (fun uu____853  ->
            if b
            then
              let uu____854 = FStar_Syntax_Print.term_to_string t in
              let uu____855 = FStar_Syntax_Print.tag_of_term t in
              FStar_Util.print2 "is_type %s (%s)\n" uu____854 uu____855
            else
              (let uu____857 = FStar_Syntax_Print.term_to_string t in
               let uu____858 = FStar_Syntax_Print.tag_of_term t in
               FStar_Util.print2 "not a type %s (%s)\n" uu____857 uu____858));
       b)
let is_type_binder env x = is_arity env (fst x).FStar_Syntax_Syntax.sort
let is_constructor: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____878 =
      let uu____879 = FStar_Syntax_Subst.compress t in
      uu____879.FStar_Syntax_Syntax.n in
    match uu____878 with
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____882;
          FStar_Syntax_Syntax.fv_delta = uu____883;
          FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor );_}
        -> true
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____884;
          FStar_Syntax_Syntax.fv_delta = uu____885;
          FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor
            uu____886);_}
        -> true
    | uu____890 -> false
let rec is_fstar_value: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____894 =
      let uu____895 = FStar_Syntax_Subst.compress t in
      uu____895.FStar_Syntax_Syntax.n in
    match uu____894 with
    | FStar_Syntax_Syntax.Tm_constant uu____898 -> true
    | FStar_Syntax_Syntax.Tm_bvar uu____899 -> true
    | FStar_Syntax_Syntax.Tm_fvar uu____900 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____901 -> true
    | FStar_Syntax_Syntax.Tm_app (head1,args) ->
        let uu____932 = is_constructor head1 in
        if uu____932
        then
          FStar_All.pipe_right args
            (FStar_List.for_all
               (fun uu____943  ->
                  match uu____943 with | (te,uu____947) -> is_fstar_value te))
        else false
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____950) -> is_fstar_value t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____956,uu____957) ->
        is_fstar_value t1
    | uu____986 -> false
let rec is_ml_value: FStar_Extraction_ML_Syntax.mlexpr -> Prims.bool =
  fun e  ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_Const uu____990 -> true
    | FStar_Extraction_ML_Syntax.MLE_Var uu____991 -> true
    | FStar_Extraction_ML_Syntax.MLE_Name uu____992 -> true
    | FStar_Extraction_ML_Syntax.MLE_Fun uu____993 -> true
    | FStar_Extraction_ML_Syntax.MLE_CTor (uu____999,exps) ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Tuple exps ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Record (uu____1005,fields) ->
        FStar_Util.for_all
          (fun uu____1020  ->
             match uu____1020 with | (uu____1023,e1) -> is_ml_value e1)
          fields
    | uu____1025 -> false
let normalize_abs: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t0  ->
    let rec aux bs t copt =
      let t1 = FStar_Syntax_Subst.compress t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_abs (bs',body,copt1) ->
          aux (FStar_List.append bs bs') body copt1
      | uu____1085 ->
          let e' = FStar_Syntax_Util.unascribe t1 in
          let uu____1087 = FStar_Syntax_Util.is_fun e' in
          if uu____1087
          then aux bs e' copt
          else FStar_Syntax_Util.abs bs e' copt in
    aux [] t0 None
let unit_binder: FStar_Syntax_Syntax.binder =
  let uu____1096 =
    FStar_Syntax_Syntax.new_bv None FStar_TypeChecker_Common.t_unit in
  FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____1096
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
      (let uu____1140 = FStar_List.hd l in
       match uu____1140 with
       | (p1,w1,e1) ->
           let uu____1159 =
             let uu____1164 = FStar_List.tl l in FStar_List.hd uu____1164 in
           (match uu____1159 with
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
                 | uu____1203 -> def)))
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
            let uu____1246 = erasable g f ty in
            if uu____1246
            then
              let uu____1247 =
                type_leq g ty FStar_Extraction_ML_Syntax.ml_unit_ty in
              (if uu____1247
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
          let uu____1263 = type_leq_c g (Some e) ty1 expect in
          match uu____1263 with
          | (true ,Some e') -> e'
          | uu____1269 ->
              (FStar_Extraction_ML_UEnv.debug g
                 (fun uu____1278  ->
                    let uu____1279 =
                      FStar_Extraction_ML_Code.string_of_mlexpr
                        g.FStar_Extraction_ML_UEnv.currentModule e in
                    let uu____1280 =
                      FStar_Extraction_ML_Code.string_of_mlty
                        g.FStar_Extraction_ML_UEnv.currentModule ty1 in
                    let uu____1281 =
                      FStar_Extraction_ML_Code.string_of_mlty
                        g.FStar_Extraction_ML_UEnv.currentModule expect in
                    FStar_Util.print3
                      "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n"
                      uu____1279 uu____1280 uu____1281);
               FStar_All.pipe_left
                 (FStar_Extraction_ML_Syntax.with_ty expect)
                 (FStar_Extraction_ML_Syntax.MLE_Coerce (e, ty1, expect)))
let bv_as_mlty:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlty
  =
  fun g  ->
    fun bv  ->
      let uu____1288 = FStar_Extraction_ML_UEnv.lookup_bv g bv in
      match uu____1288 with
      | FStar_Util.Inl (uu____1289,t) -> t
      | uu____1297 -> FStar_Extraction_ML_Syntax.MLTY_Top
let rec term_as_mlty:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlty
  =
  fun g  ->
    fun t0  ->
      let rec is_top_ty t =
        match t with
        | FStar_Extraction_ML_Syntax.MLTY_Top  -> true
        | FStar_Extraction_ML_Syntax.MLTY_Named uu____1333 ->
            let uu____1337 = FStar_Extraction_ML_Util.udelta_unfold g t in
            (match uu____1337 with | None  -> false | Some t1 -> is_top_ty t1)
        | uu____1340 -> false in
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
      let uu____1343 = is_top_ty mlt in
      if uu____1343
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
      | FStar_Syntax_Syntax.Tm_bvar uu____1349 ->
          let uu____1350 =
            let uu____1351 = FStar_Syntax_Print.term_to_string t1 in
            FStar_Util.format1 "Impossible: Unexpected term %s" uu____1351 in
          failwith uu____1350
      | FStar_Syntax_Syntax.Tm_delayed uu____1352 ->
          let uu____1373 =
            let uu____1374 = FStar_Syntax_Print.term_to_string t1 in
            FStar_Util.format1 "Impossible: Unexpected term %s" uu____1374 in
          failwith uu____1373
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____1375 =
            let uu____1376 = FStar_Syntax_Print.term_to_string t1 in
            FStar_Util.format1 "Impossible: Unexpected term %s" uu____1376 in
          failwith uu____1375
      | FStar_Syntax_Syntax.Tm_constant uu____1377 ->
          FStar_Extraction_ML_UEnv.unknownType
      | FStar_Syntax_Syntax.Tm_uvar uu____1378 ->
          FStar_Extraction_ML_UEnv.unknownType
      | FStar_Syntax_Syntax.Tm_meta (t2,uu____1390) -> term_as_mlty' env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____1395;
             FStar_Syntax_Syntax.index = uu____1396;
             FStar_Syntax_Syntax.sort = t2;_},uu____1398)
          -> term_as_mlty' env t2
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____1406) -> term_as_mlty' env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____1412,uu____1413) ->
          term_as_mlty' env t2
      | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
      | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv []
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____1460 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____1460 with
           | (bs1,c1) ->
               let uu____1465 = binders_as_ml_binders env bs1 in
               (match uu____1465 with
                | (mlbs,env1) ->
                    let t_ret =
                      let eff =
                        FStar_TypeChecker_Env.norm_eff_name
                          env1.FStar_Extraction_ML_UEnv.tcenv
                          (FStar_Syntax_Util.comp_effect_name c1) in
                      let uu____1481 =
                        let uu____1485 =
                          FStar_TypeChecker_Env.effect_decl_opt
                            env1.FStar_Extraction_ML_UEnv.tcenv eff in
                        FStar_Util.must uu____1485 in
                      match uu____1481 with
                      | (ed,qualifiers) ->
                          let uu____1497 =
                            FStar_All.pipe_right qualifiers
                              (FStar_List.contains
                                 FStar_Syntax_Syntax.Reifiable) in
                          if uu____1497
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
                    let uu____1503 =
                      FStar_List.fold_right
                        (fun uu____1516  ->
                           fun uu____1517  ->
                             match (uu____1516, uu____1517) with
                             | ((uu____1528,t2),(tag,t')) ->
                                 (FStar_Extraction_ML_Syntax.E_PURE,
                                   (FStar_Extraction_ML_Syntax.MLTY_Fun
                                      (t2, tag, t')))) mlbs (erase1, t_ret) in
                    (match uu____1503 with | (uu____1536,t2) -> t2)))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let res =
            let uu____1555 =
              let uu____1556 = FStar_Syntax_Util.un_uinst head1 in
              uu____1556.FStar_Syntax_Syntax.n in
            match uu____1555 with
            | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
            | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv args
            | FStar_Syntax_Syntax.Tm_app (head2,args') ->
                let uu____1577 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app
                       (head2, (FStar_List.append args' args))) None
                    t1.FStar_Syntax_Syntax.pos in
                term_as_mlty' env uu____1577
            | uu____1593 -> FStar_Extraction_ML_UEnv.unknownType in
          res
      | FStar_Syntax_Syntax.Tm_abs (bs,ty,uu____1596) ->
          let uu____1619 = FStar_Syntax_Subst.open_term bs ty in
          (match uu____1619 with
           | (bs1,ty1) ->
               let uu____1624 = binders_as_ml_binders env bs1 in
               (match uu____1624 with | (bts,env1) -> term_as_mlty' env1 ty1))
      | FStar_Syntax_Syntax.Tm_type uu____1638 ->
          FStar_Extraction_ML_UEnv.unknownType
      | FStar_Syntax_Syntax.Tm_let uu____1639 ->
          FStar_Extraction_ML_UEnv.unknownType
      | FStar_Syntax_Syntax.Tm_match uu____1647 ->
          FStar_Extraction_ML_UEnv.unknownType
and arg_as_mlty:
  FStar_Extraction_ML_UEnv.env ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.aqual) ->
      FStar_Extraction_ML_Syntax.mlty
  =
  fun g  ->
    fun uu____1663  ->
      match uu____1663 with
      | (a,uu____1667) ->
          let uu____1668 = is_type g a in
          if uu____1668
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
        let uu____1673 =
          let uu____1681 =
            FStar_TypeChecker_Env.lookup_lid g.FStar_Extraction_ML_UEnv.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____1681 with
          | ((uu____1693,ty),uu____1695) ->
              FStar_Syntax_Util.arrow_formals ty in
        match uu____1673 with
        | (formals,t) ->
            let mlargs = FStar_List.map (arg_as_mlty g) args in
            let mlargs1 =
              let n_args = FStar_List.length args in
              if (FStar_List.length formals) > n_args
              then
                let uu____1730 = FStar_Util.first_N n_args formals in
                match uu____1730 with
                | (uu____1744,rest) ->
                    let uu____1758 =
                      FStar_List.map
                        (fun uu____1763  ->
                           FStar_Extraction_ML_UEnv.erasedContent) rest in
                    FStar_List.append mlargs uu____1758
              else mlargs in
            let nm =
              let uu____1768 =
                FStar_Extraction_ML_UEnv.maybe_mangle_type_projector g fv in
              match uu____1768 with
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
      let uu____1779 =
        FStar_All.pipe_right bs
          (FStar_List.fold_left
             (fun uu____1811  ->
                fun b  ->
                  match uu____1811 with
                  | (ml_bs,env) ->
                      let uu____1841 = is_type_binder g b in
                      if uu____1841
                      then
                        let b1 = fst b in
                        let env1 =
                          FStar_Extraction_ML_UEnv.extend_ty env b1
                            (Some FStar_Extraction_ML_Syntax.MLTY_Top) in
                        let ml_b =
                          let uu____1856 =
                            FStar_Extraction_ML_UEnv.bv_as_ml_termvar b1 in
                          (uu____1856, FStar_Extraction_ML_Syntax.ml_unit_ty) in
                        ((ml_b :: ml_bs), env1)
                      else
                        (let b1 = fst b in
                         let t = term_as_mlty env b1.FStar_Syntax_Syntax.sort in
                         let uu____1873 =
                           FStar_Extraction_ML_UEnv.extend_bv env b1 
                             ([], t) false false false in
                         match uu____1873 with
                         | (env1,b2) ->
                             let ml_b =
                               let uu____1891 =
                                 FStar_Extraction_ML_UEnv.removeTick b2 in
                               (uu____1891, t) in
                             ((ml_b :: ml_bs), env1))) ([], g)) in
      match uu____1779 with | (ml_bs,env) -> ((FStar_List.rev ml_bs), env)
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
      | (FStar_Extraction_ML_Syntax.MLE_Seq es1,uu____1951) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (FStar_List.append es1 [e2])
      | (uu____1953,FStar_Extraction_ML_Syntax.MLE_Seq es2) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (e1 :: es2)
      | uu____1956 -> FStar_Extraction_ML_Syntax.MLE_Seq [e1; e2]
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
                    | uu____1978 when
                        (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
                          =
                          FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr
                        -> body.FStar_Extraction_ML_Syntax.expr
                    | uu____1979 ->
                        mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def
                          body)
             | uu____1980 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body))
        | uu____1982 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body)
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
           | uu____1996 ->
               (match q with
                | Some (FStar_Syntax_Syntax.Record_ctor (ty,fns)) ->
                    let path =
                      FStar_List.map FStar_Ident.text_of_id ty.FStar_Ident.ns in
                    let fs = record_fields fns pats in
                    FStar_Extraction_ML_Syntax.MLP_Record (path, fs)
                | uu____2012 -> p))
      | uu____2014 -> p
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
                     (fun uu____2053  ->
                        let uu____2054 =
                          FStar_Extraction_ML_Code.string_of_mlty
                            g.FStar_Extraction_ML_UEnv.currentModule t' in
                        let uu____2055 =
                          FStar_Extraction_ML_Code.string_of_mlty
                            g.FStar_Extraction_ML_UEnv.currentModule t in
                        FStar_Util.print2
                          "Expected pattern type %s; got pattern type %s\n"
                          uu____2054 uu____2055)
                 else ();
                 ok) in
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int
              (c,None )) ->
              let i = FStar_Const.Const_int (c, None) in
              let x = FStar_Extraction_ML_Syntax.gensym () in
              let when_clause =
                let uu____2078 =
                  let uu____2079 =
                    let uu____2083 =
                      let uu____2085 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.ml_int_ty)
                          (FStar_Extraction_ML_Syntax.MLE_Var x) in
                      let uu____2086 =
                        let uu____2088 =
                          let uu____2089 =
                            let uu____2090 =
                              FStar_Extraction_ML_Util.mlconst_of_const'
                                p.FStar_Syntax_Syntax.p i in
                            FStar_All.pipe_left
                              (fun _0_31  ->
                                 FStar_Extraction_ML_Syntax.MLE_Const _0_31)
                              uu____2090 in
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty
                               FStar_Extraction_ML_Syntax.ml_int_ty)
                            uu____2089 in
                        [uu____2088] in
                      uu____2085 :: uu____2086 in
                    (FStar_Extraction_ML_Util.prims_op_equality, uu____2083) in
                  FStar_Extraction_ML_Syntax.MLE_App uu____2079 in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     FStar_Extraction_ML_Syntax.ml_bool_ty) uu____2078 in
              let uu____2092 = ok FStar_Extraction_ML_Syntax.ml_int_ty in
              (g,
                (Some ((FStar_Extraction_ML_Syntax.MLP_Var x), [when_clause])),
                uu____2092)
          | FStar_Syntax_Syntax.Pat_constant s ->
              let t =
                FStar_TypeChecker_TcTerm.tc_constant FStar_Range.dummyRange s in
              let mlty = term_as_mlty g t in
              let uu____2104 =
                let uu____2109 =
                  let uu____2113 =
                    let uu____2114 =
                      FStar_Extraction_ML_Util.mlconst_of_const'
                        p.FStar_Syntax_Syntax.p s in
                    FStar_Extraction_ML_Syntax.MLP_Const uu____2114 in
                  (uu____2113, []) in
                Some uu____2109 in
              let uu____2119 = ok mlty in (g, uu____2104, uu____2119)
          | FStar_Syntax_Syntax.Pat_var x ->
              let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort in
              let uu____2126 =
                FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false false
                  imp in
              (match uu____2126 with
               | (g1,x1) ->
                   let uu____2139 = ok mlty in
                   (g1,
                     (if imp
                      then None
                      else Some ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                     uu____2139))
          | FStar_Syntax_Syntax.Pat_wild x ->
              let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort in
              let uu____2158 =
                FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false false
                  imp in
              (match uu____2158 with
               | (g1,x1) ->
                   let uu____2171 = ok mlty in
                   (g1,
                     (if imp
                      then None
                      else Some ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                     uu____2171))
          | FStar_Syntax_Syntax.Pat_dot_term uu____2188 -> (g, None, true)
          | FStar_Syntax_Syntax.Pat_cons (f,pats) ->
              let uu____2210 =
                let uu____2213 = FStar_Extraction_ML_UEnv.lookup_fv g f in
                match uu____2213 with
                | FStar_Util.Inr
                    (uu____2216,{
                                  FStar_Extraction_ML_Syntax.expr =
                                    FStar_Extraction_ML_Syntax.MLE_Name n1;
                                  FStar_Extraction_ML_Syntax.mlty =
                                    uu____2218;
                                  FStar_Extraction_ML_Syntax.loc = uu____2219;_},ttys,uu____2221)
                    -> (n1, ttys)
                | uu____2228 -> failwith "Expected a constructor" in
              (match uu____2210 with
               | (d,tys) ->
                   let nTyVars = FStar_List.length (fst tys) in
                   let uu____2242 = FStar_Util.first_N nTyVars pats in
                   (match uu____2242 with
                    | (tysVarPats,restPats) ->
                        let f_ty_opt =
                          try
                            let mlty_args =
                              FStar_All.pipe_right tysVarPats
                                (FStar_List.map
                                   (fun uu____2316  ->
                                      match uu____2316 with
                                      | (p1,uu____2321) ->
                                          (match p1.FStar_Syntax_Syntax.v
                                           with
                                           | FStar_Syntax_Syntax.Pat_dot_term
                                               (uu____2324,t) ->
                                               term_as_mlty g t
                                           | uu____2330 ->
                                               (FStar_Extraction_ML_UEnv.debug
                                                  g
                                                  (fun uu____2334  ->
                                                     let uu____2335 =
                                                       FStar_Syntax_Print.pat_to_string
                                                         p1 in
                                                     FStar_Util.print1
                                                       "Pattern %s is not extractable"
                                                       uu____2335);
                                                raise Un_extractable)))) in
                            let f_ty =
                              FStar_Extraction_ML_Util.subst tys mlty_args in
                            let uu____2337 =
                              FStar_Extraction_ML_Util.uncurry_mlty_fun f_ty in
                            Some uu____2337
                          with | Un_extractable  -> None in
                        let uu____2353 =
                          FStar_Util.fold_map
                            (fun g1  ->
                               fun uu____2376  ->
                                 match uu____2376 with
                                 | (p1,imp1) ->
                                     let uu____2387 =
                                       extract_one_pat true g1 p1 None in
                                     (match uu____2387 with
                                      | (g2,p2,uu____2403) -> (g2, p2))) g
                            tysVarPats in
                        (match uu____2353 with
                         | (g1,tyMLPats) ->
                             let uu____2435 =
                               FStar_Util.fold_map
                                 (fun uu____2474  ->
                                    fun uu____2475  ->
                                      match (uu____2474, uu____2475) with
                                      | ((g2,f_ty_opt1),(p1,imp1)) ->
                                          let uu____2524 =
                                            match f_ty_opt1 with
                                            | Some (hd1::rest,res) ->
                                                ((Some (rest, res)),
                                                  (Some hd1))
                                            | uu____2556 -> (None, None) in
                                          (match uu____2524 with
                                           | (f_ty_opt2,expected_ty) ->
                                               let uu____2593 =
                                                 extract_one_pat false g2 p1
                                                   expected_ty in
                                               (match uu____2593 with
                                                | (g3,p2,uu____2615) ->
                                                    ((g3, f_ty_opt2), p2))))
                                 (g1, f_ty_opt) restPats in
                             (match uu____2435 with
                              | ((g2,f_ty_opt1),restMLPats) ->
                                  let uu____2676 =
                                    let uu____2682 =
                                      FStar_All.pipe_right
                                        (FStar_List.append tyMLPats
                                           restMLPats)
                                        (FStar_List.collect
                                           (fun uu___137_2709  ->
                                              match uu___137_2709 with
                                              | Some x -> [x]
                                              | uu____2731 -> [])) in
                                    FStar_All.pipe_right uu____2682
                                      FStar_List.split in
                                  (match uu____2676 with
                                   | (mlPats,when_clauses) ->
                                       let pat_ty_compat =
                                         match f_ty_opt1 with
                                         | Some ([],t) -> ok t
                                         | uu____2770 -> false in
                                       let uu____2775 =
                                         let uu____2780 =
                                           let uu____2784 =
                                             resugar_pat
                                               f.FStar_Syntax_Syntax.fv_qual
                                               (FStar_Extraction_ML_Syntax.MLP_CTor
                                                  (d, mlPats)) in
                                           let uu____2786 =
                                             FStar_All.pipe_right
                                               when_clauses
                                               FStar_List.flatten in
                                           (uu____2784, uu____2786) in
                                         Some uu____2780 in
                                       (g2, uu____2775, pat_ty_compat))))))
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
          let uu____2840 = extract_one_pat false g1 p1 expected_t1 in
          match uu____2840 with
          | (g2,Some (x,v1),b) -> (g2, (x, v1), b)
          | uu____2871 -> failwith "Impossible: Unable to translate pattern" in
        let mk_when_clause whens =
          match whens with
          | [] -> None
          | hd1::tl1 ->
              let uu____2896 =
                FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd1 tl1 in
              Some uu____2896 in
        let uu____2897 = extract_one_pat1 g p (Some expected_t) in
        match uu____2897 with
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
            | FStar_Extraction_ML_Syntax.MLTY_Fun (t0,uu____2979,t1) ->
                let x = FStar_Extraction_ML_Syntax.gensym () in
                let uu____2982 =
                  let uu____2988 =
                    let uu____2993 =
                      FStar_All.pipe_left
                        (FStar_Extraction_ML_Syntax.with_ty t0)
                        (FStar_Extraction_ML_Syntax.MLE_Var x) in
                    ((x, t0), uu____2993) in
                  uu____2988 :: more_args in
                eta_args uu____2982 t1
            | FStar_Extraction_ML_Syntax.MLTY_Named (uu____3000,uu____3001)
                -> ((FStar_List.rev more_args), t)
            | uu____3013 -> failwith "Impossible: Head type is not an arrow" in
          let as_record qual1 e =
            match ((e.FStar_Extraction_ML_Syntax.expr), qual1) with
            | (FStar_Extraction_ML_Syntax.MLE_CTor (uu____3031,args),Some
               (FStar_Syntax_Syntax.Record_ctor (tyname,fields))) ->
                let path =
                  FStar_List.map FStar_Ident.text_of_id tyname.FStar_Ident.ns in
                let fields1 = record_fields fields args in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     e.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_Record (path, fields1))
            | uu____3050 -> e in
          let resugar_and_maybe_eta qual1 e =
            let uu____3063 = eta_args [] residualType in
            match uu____3063 with
            | (eargs,tres) ->
                (match eargs with
                 | [] ->
                     let uu____3091 = as_record qual1 e in
                     FStar_Extraction_ML_Util.resugar_exp uu____3091
                 | uu____3092 ->
                     let uu____3098 = FStar_List.unzip eargs in
                     (match uu____3098 with
                      | (binders,eargs1) ->
                          (match e.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_CTor (head1,args)
                               ->
                               let body =
                                 let uu____3122 =
                                   let uu____3123 =
                                     FStar_All.pipe_left
                                       (FStar_Extraction_ML_Syntax.with_ty
                                          tres)
                                       (FStar_Extraction_ML_Syntax.MLE_CTor
                                          (head1,
                                            (FStar_List.append args eargs1))) in
                                   FStar_All.pipe_left (as_record qual1)
                                     uu____3123 in
                                 FStar_All.pipe_left
                                   FStar_Extraction_ML_Util.resugar_exp
                                   uu____3122 in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    e.FStar_Extraction_ML_Syntax.mlty)
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    (binders, body))
                           | uu____3128 ->
                               failwith "Impossible: Not a constructor"))) in
          match ((mlAppExpr.FStar_Extraction_ML_Syntax.expr), qual) with
          | (uu____3130,None ) -> mlAppExpr
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____3133;
                FStar_Extraction_ML_Syntax.loc = uu____3134;_},mle::args),Some
             (FStar_Syntax_Syntax.Record_projector (constrname,f))) ->
              let f1 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append constrname.FStar_Ident.ns [f]) in
              let fn = FStar_Extraction_ML_Util.mlpath_of_lid f1 in
              let proj = FStar_Extraction_ML_Syntax.MLE_Proj (mle, fn) in
              let e =
                match args with
                | [] -> proj
                | uu____3152 ->
                    let uu____3154 =
                      let uu____3158 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj in
                      (uu____3158, args) in
                    FStar_Extraction_ML_Syntax.MLE_App uu____3154 in
              FStar_Extraction_ML_Syntax.with_ty
                mlAppExpr.FStar_Extraction_ML_Syntax.mlty e
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____3161;
                FStar_Extraction_ML_Syntax.loc = uu____3162;_},mlargs),Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____3167 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs)) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____3167
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____3170;
                FStar_Extraction_ML_Syntax.loc = uu____3171;_},mlargs),Some
             (FStar_Syntax_Syntax.Record_ctor uu____3173)) ->
              let uu____3180 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs)) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____3180
          | (FStar_Extraction_ML_Syntax.MLE_Name mlp,Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____3184 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, [])) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____3184
          | (FStar_Extraction_ML_Syntax.MLE_Name mlp,Some
             (FStar_Syntax_Syntax.Record_ctor uu____3187)) ->
              let uu____3192 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, [])) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____3192
          | uu____3194 -> mlAppExpr
let maybe_downgrade_eff:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.e_tag ->
      FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.e_tag
  =
  fun g  ->
    fun f  ->
      fun t  ->
        let uu____3207 =
          (f = FStar_Extraction_ML_Syntax.E_GHOST) &&
            (type_leq g t FStar_Extraction_ML_Syntax.ml_unit_ty) in
        if uu____3207 then FStar_Extraction_ML_Syntax.E_PURE else f
let rec term_as_mlexpr:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Extraction_ML_Syntax.mlexpr* FStar_Extraction_ML_Syntax.e_tag*
        FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun t  ->
      let uu____3248 = term_as_mlexpr' g t in
      match uu____3248 with
      | (e,tag,ty) ->
          let tag1 = maybe_downgrade_eff g tag ty in
          (FStar_Extraction_ML_UEnv.debug g
             (fun u  ->
                let uu____3263 =
                  let uu____3264 = FStar_Syntax_Print.tag_of_term t in
                  let uu____3265 = FStar_Syntax_Print.term_to_string t in
                  let uu____3266 =
                    FStar_Extraction_ML_Code.string_of_mlty
                      g.FStar_Extraction_ML_UEnv.currentModule ty in
                  FStar_Util.format4
                    "term_as_mlexpr (%s) :  %s has ML type %s and effect %s\n"
                    uu____3264 uu____3265 uu____3266
                    (FStar_Extraction_ML_Util.eff_to_string tag1) in
                FStar_Util.print_string uu____3263);
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
          let uu____3273 = check_term_as_mlexpr' g t f ty in
          match uu____3273 with
          | (e,t1) ->
              let uu____3280 = erase g e t1 f in
              (match uu____3280 with | (r,uu____3287,t2) -> (r, t2))
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
          let uu____3295 = term_as_mlexpr g e0 in
          match uu____3295 with
          | (e,tag,t) ->
              let tag1 = maybe_downgrade_eff g tag t in
              if FStar_Extraction_ML_Util.eff_leq tag1 f
              then let uu____3307 = maybe_coerce g e t ty in (uu____3307, ty)
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
           let uu____3320 =
             let uu____3321 =
               FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos in
             let uu____3322 = FStar_Syntax_Print.tag_of_term top in
             let uu____3323 = FStar_Syntax_Print.term_to_string top in
             FStar_Util.format3 "%s: term_as_mlexpr' (%s) :  %s \n"
               uu____3321 uu____3322 uu____3323 in
           FStar_Util.print_string uu____3320);
      (let t = FStar_Syntax_Subst.compress top in
       match t.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____3328 =
             let uu____3329 = FStar_Syntax_Print.tag_of_term t in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____3329 in
           failwith uu____3328
       | FStar_Syntax_Syntax.Tm_delayed uu____3333 ->
           let uu____3354 =
             let uu____3355 = FStar_Syntax_Print.tag_of_term t in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____3355 in
           failwith uu____3354
       | FStar_Syntax_Syntax.Tm_uvar uu____3359 ->
           let uu____3370 =
             let uu____3371 = FStar_Syntax_Print.tag_of_term t in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____3371 in
           failwith uu____3370
       | FStar_Syntax_Syntax.Tm_bvar uu____3375 ->
           let uu____3376 =
             let uu____3377 = FStar_Syntax_Print.tag_of_term t in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____3377 in
           failwith uu____3376
       | FStar_Syntax_Syntax.Tm_type uu____3381 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_refine uu____3382 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_arrow uu____3387 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Mutable_alloc ))
           ->
           let uu____3400 = term_as_mlexpr' g t1 in
           (match uu____3400 with
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
            | uu____3427 -> failwith "impossible")
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_monadic (m,uu____3436)) ->
           let t2 = FStar_Syntax_Subst.compress t1 in
           (match t2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) when
                FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname ->
                let uu____3459 =
                  let uu____3463 =
                    FStar_TypeChecker_Env.effect_decl_opt
                      g.FStar_Extraction_ML_UEnv.tcenv m in
                  FStar_Util.must uu____3463 in
                (match uu____3459 with
                 | (ed,qualifiers) ->
                     let uu____3478 =
                       let uu____3479 =
                         FStar_All.pipe_right qualifiers
                           (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
                       FStar_All.pipe_right uu____3479 Prims.op_Negation in
                     if uu____3478
                     then term_as_mlexpr' g t2
                     else
                       failwith
                         "This should not happen (should have been handled at Tm_abs level)")
            | uu____3488 -> term_as_mlexpr' g t2)
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____3490) -> term_as_mlexpr' g t1
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____3496) -> term_as_mlexpr' g t1
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____3502 =
             FStar_TypeChecker_TcTerm.type_of_tot_term
               g.FStar_Extraction_ML_UEnv.tcenv t in
           (match uu____3502 with
            | (uu____3509,ty,uu____3511) ->
                let ml_ty = term_as_mlty g ty in
                let uu____3513 =
                  let uu____3514 =
                    let uu____3515 =
                      FStar_Extraction_ML_Util.mlconst_of_const'
                        t.FStar_Syntax_Syntax.pos c in
                    FStar_All.pipe_left
                      (fun _0_32  ->
                         FStar_Extraction_ML_Syntax.MLE_Const _0_32)
                      uu____3515 in
                  FStar_Extraction_ML_Syntax.with_ty ml_ty uu____3514 in
                (uu____3513, FStar_Extraction_ML_Syntax.E_PURE, ml_ty))
       | FStar_Syntax_Syntax.Tm_name uu____3516 ->
           let uu____3517 = is_type g t in
           if uu____3517
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____3522 = FStar_Extraction_ML_UEnv.lookup_term g t in
              match uu____3522 with
              | (FStar_Util.Inl uu____3529,uu____3530) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | (FStar_Util.Inr (uu____3549,x,mltys,uu____3552),qual) ->
                  (match mltys with
                   | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                       ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | ([],t1) ->
                       let uu____3577 =
                         maybe_eta_data_and_project_record g qual t1 x in
                       (uu____3577, FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | uu____3578 -> err_uninst g t mltys t))
       | FStar_Syntax_Syntax.Tm_fvar uu____3582 ->
           let uu____3583 = is_type g t in
           if uu____3583
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____3588 = FStar_Extraction_ML_UEnv.lookup_term g t in
              match uu____3588 with
              | (FStar_Util.Inl uu____3595,uu____3596) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | (FStar_Util.Inr (uu____3615,x,mltys,uu____3618),qual) ->
                  (match mltys with
                   | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                       ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | ([],t1) ->
                       let uu____3643 =
                         maybe_eta_data_and_project_record g qual t1 x in
                       (uu____3643, FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | uu____3644 -> err_uninst g t mltys t))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,copt) ->
           let uu____3673 = FStar_Syntax_Subst.open_term bs body in
           (match uu____3673 with
            | (bs1,body1) ->
                let uu____3681 = binders_as_ml_binders g bs1 in
                (match uu____3681 with
                 | (ml_bs,env) ->
                     let body2 =
                       match copt with
                       | Some c ->
                           (FStar_Extraction_ML_UEnv.debug g
                              (fun uu____3714  ->
                                 match c with
                                 | FStar_Util.Inl lc ->
                                     let uu____3719 =
                                       FStar_Syntax_Print.lcomp_to_string lc in
                                     FStar_Util.print1 "Computation lc: %s\n"
                                       uu____3719
                                 | FStar_Util.Inr rc ->
                                     FStar_Util.print1 "Computation rc: %s\n"
                                       (FStar_Ident.text_of_lid (fst rc)));
                            (let uu____3728 =
                               FStar_TypeChecker_Env.is_reifiable
                                 env.FStar_Extraction_ML_UEnv.tcenv c in
                             if uu____3728
                             then
                               FStar_TypeChecker_Util.reify_body
                                 env.FStar_Extraction_ML_UEnv.tcenv body1
                             else body1))
                       | None  ->
                           (FStar_Extraction_ML_UEnv.debug g
                              (fun uu____3738  ->
                                 let uu____3739 =
                                   FStar_Syntax_Print.term_to_string body1 in
                                 FStar_Util.print1
                                   "No computation type for: %s\n" uu____3739);
                            body1) in
                     let uu____3740 = term_as_mlexpr env body2 in
                     (match uu____3740 with
                      | (ml_body,f,t1) ->
                          let uu____3750 =
                            FStar_List.fold_right
                              (fun uu____3763  ->
                                 fun uu____3764  ->
                                   match (uu____3763, uu____3764) with
                                   | ((uu____3775,targ),(f1,t2)) ->
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         (FStar_Extraction_ML_Syntax.MLTY_Fun
                                            (targ, f1, t2)))) ml_bs (f, t1) in
                          (match uu____3750 with
                           | (f1,tfun) ->
                               let uu____3788 =
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty tfun)
                                   (FStar_Extraction_ML_Syntax.MLE_Fun
                                      (ml_bs, ml_body)) in
                               (uu____3788, f1, tfun)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____3792);
              FStar_Syntax_Syntax.tk = uu____3793;
              FStar_Syntax_Syntax.pos = uu____3794;
              FStar_Syntax_Syntax.vars = uu____3795;_},uu____3796)
           -> failwith "Unreachable? Tm_app Const_reflect"
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let is_total uu___139_3838 =
             match uu___139_3838 with
             | FStar_Util.Inl l -> FStar_Syntax_Util.is_total_lcomp l
             | FStar_Util.Inr (l,flags) ->
                 (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid)
                   ||
                   (FStar_All.pipe_right flags
                      (FStar_List.existsb
                         (fun uu___138_3857  ->
                            match uu___138_3857 with
                            | FStar_Syntax_Syntax.TOTAL  -> true
                            | uu____3858 -> false))) in
           let uu____3859 =
             let uu____3862 =
               let uu____3863 = FStar_Syntax_Subst.compress head1 in
               uu____3863.FStar_Syntax_Syntax.n in
             ((head1.FStar_Syntax_Syntax.n), uu____3862) in
           (match uu____3859 with
            | (FStar_Syntax_Syntax.Tm_uvar uu____3869,uu____3870) ->
                let t1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.Iota;
                    FStar_TypeChecker_Normalize.Zeta;
                    FStar_TypeChecker_Normalize.EraseUniverses;
                    FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                    g.FStar_Extraction_ML_UEnv.tcenv t in
                term_as_mlexpr' g t1
            | (uu____3882,FStar_Syntax_Syntax.Tm_abs (bs,uu____3884,Some lc))
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
            | (uu____3913,FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_reify )) ->
                let e =
                  let uu____3915 = FStar_List.hd args in
                  FStar_TypeChecker_Util.reify_body_with_arg
                    g.FStar_Extraction_ML_UEnv.tcenv head1 uu____3915 in
                let tm =
                  let uu____3923 =
                    let uu____3924 = FStar_TypeChecker_Util.remove_reify e in
                    let uu____3925 = FStar_List.tl args in
                    FStar_Syntax_Syntax.mk_Tm_app uu____3924 uu____3925 in
                  uu____3923 None t.FStar_Syntax_Syntax.pos in
                term_as_mlexpr' g tm
            | uu____3934 ->
                let rec extract_app is_data uu____3962 uu____3963 restArgs =
                  match (uu____3962, uu____3963) with
                  | ((mlhead,mlargs_f),(f,t1)) ->
                      (match (restArgs, t1) with
                       | ([],uu____4011) ->
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
                                | uu____4026 -> false) in
                           let uu____4027 =
                             if evaluation_order_guaranteed
                             then
                               let uu____4040 =
                                 FStar_All.pipe_right
                                   (FStar_List.rev mlargs_f)
                                   (FStar_List.map FStar_Pervasives.fst) in
                               ([], uu____4040)
                             else
                               FStar_List.fold_left
                                 (fun uu____4071  ->
                                    fun uu____4072  ->
                                      match (uu____4071, uu____4072) with
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
                                             let uu____4127 =
                                               let uu____4129 =
                                                 FStar_All.pipe_left
                                                   (FStar_Extraction_ML_Syntax.with_ty
                                                      arg.FStar_Extraction_ML_Syntax.mlty)
                                                   (FStar_Extraction_ML_Syntax.MLE_Var
                                                      x) in
                                               uu____4129 :: out_args in
                                             (((x, arg) :: lbs), uu____4127)))
                                 ([], []) mlargs_f in
                           (match uu____4027 with
                            | (lbs,mlargs) ->
                                let app =
                                  let uu____4156 =
                                    FStar_All.pipe_left
                                      (FStar_Extraction_ML_Syntax.with_ty t1)
                                      (FStar_Extraction_ML_Syntax.MLE_App
                                         (mlhead, mlargs)) in
                                  FStar_All.pipe_left
                                    (maybe_eta_data_and_project_record g
                                       is_data t1) uu____4156 in
                                let l_app =
                                  FStar_List.fold_right
                                    (fun uu____4165  ->
                                       fun out  ->
                                         match uu____4165 with
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
                       | ((arg,uu____4178)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                          (formal_t,f',t2)) when
                           (is_type g arg) &&
                             (type_leq g formal_t
                                FStar_Extraction_ML_Syntax.ml_unit_ty)
                           ->
                           let uu____4196 =
                             let uu____4199 =
                               FStar_Extraction_ML_Util.join
                                 arg.FStar_Syntax_Syntax.pos f f' in
                             (uu____4199, t2) in
                           extract_app is_data
                             (mlhead,
                               ((FStar_Extraction_ML_Syntax.ml_unit,
                                  FStar_Extraction_ML_Syntax.E_PURE) ::
                               mlargs_f)) uu____4196 rest
                       | ((e0,uu____4206)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                          (tExpected,f',t2)) ->
                           let r = e0.FStar_Syntax_Syntax.pos in
                           let uu____4225 = term_as_mlexpr g e0 in
                           (match uu____4225 with
                            | (e01,f0,tInferred) ->
                                let e02 =
                                  maybe_coerce g e01 tInferred tExpected in
                                let uu____4236 =
                                  let uu____4239 =
                                    FStar_Extraction_ML_Util.join_l r
                                      [f; f'; f0] in
                                  (uu____4239, t2) in
                                extract_app is_data
                                  (mlhead, ((e02, f0) :: mlargs_f))
                                  uu____4236 rest)
                       | uu____4245 ->
                           let uu____4252 =
                             FStar_Extraction_ML_Util.udelta_unfold g t1 in
                           (match uu____4252 with
                            | Some t2 ->
                                extract_app is_data (mlhead, mlargs_f)
                                  (f, t2) restArgs
                            | None  ->
                                err_ill_typed_application g top restArgs t1)) in
                let extract_app_maybe_projector is_data mlhead uu____4288
                  args1 =
                  match uu____4288 with
                  | (f,t1) ->
                      (match is_data with
                       | Some (FStar_Syntax_Syntax.Record_projector
                           uu____4307) ->
                           let rec remove_implicits args2 f1 t2 =
                             match (args2, t2) with
                             | ((a0,Some (FStar_Syntax_Syntax.Implicit
                                 uu____4357))::args3,FStar_Extraction_ML_Syntax.MLTY_Fun
                                (uu____4359,f',t3)) ->
                                 let uu____4384 =
                                   FStar_Extraction_ML_Util.join
                                     a0.FStar_Syntax_Syntax.pos f1 f' in
                                 remove_implicits args3 uu____4384 t3
                             | uu____4385 -> (args2, f1, t2) in
                           let uu____4400 = remove_implicits args1 f t1 in
                           (match uu____4400 with
                            | (args2,f1,t2) ->
                                extract_app is_data (mlhead, []) (f1, t2)
                                  args2)
                       | uu____4433 ->
                           extract_app is_data (mlhead, []) (f, t1) args1) in
                let uu____4440 = is_type g t in
                if uu____4440
                then
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
                else
                  (let head2 = FStar_Syntax_Util.un_uinst head1 in
                   match head2.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_name uu____4449 ->
                       let uu____4450 =
                         let uu____4457 =
                           FStar_Extraction_ML_UEnv.lookup_term g head2 in
                         match uu____4457 with
                         | (FStar_Util.Inr (uu____4467,x1,x2,x3),q) ->
                             ((x1, x2, x3), q)
                         | uu____4492 -> failwith "FIXME Ty" in
                       (match uu____4450 with
                        | ((head_ml,(vars,t1),inst_ok),qual) ->
                            let has_typ_apps =
                              match args with
                              | (a,uu____4521)::uu____4522 -> is_type g a
                              | uu____4536 -> false in
                            let uu____4542 =
                              match vars with
                              | uu____4559::uu____4560 when
                                  (Prims.op_Negation has_typ_apps) && inst_ok
                                  -> (head_ml, t1, args)
                              | uu____4567 ->
                                  let n1 = FStar_List.length vars in
                                  if n1 <= (FStar_List.length args)
                                  then
                                    let uu____4587 =
                                      FStar_Util.first_N n1 args in
                                    (match uu____4587 with
                                     | (prefix1,rest) ->
                                         let prefixAsMLTypes =
                                           FStar_List.map
                                             (fun uu____4643  ->
                                                match uu____4643 with
                                                | (x,uu____4647) ->
                                                    term_as_mlty g x) prefix1 in
                                         let t2 =
                                           instantiate (vars, t1)
                                             prefixAsMLTypes in
                                         let head3 =
                                           match head_ml.FStar_Extraction_ML_Syntax.expr
                                           with
                                           | FStar_Extraction_ML_Syntax.MLE_Name
                                               uu____4650 ->
                                               let uu___143_4651 = head_ml in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (uu___143_4651.FStar_Extraction_ML_Syntax.expr);
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   = t2;
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___143_4651.FStar_Extraction_ML_Syntax.loc)
                                               }
                                           | FStar_Extraction_ML_Syntax.MLE_Var
                                               uu____4652 ->
                                               let uu___143_4653 = head_ml in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (uu___143_4653.FStar_Extraction_ML_Syntax.expr);
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   = t2;
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___143_4653.FStar_Extraction_ML_Syntax.loc)
                                               }
                                           | FStar_Extraction_ML_Syntax.MLE_App
                                               (head3,{
                                                        FStar_Extraction_ML_Syntax.expr
                                                          =
                                                          FStar_Extraction_ML_Syntax.MLE_Const
                                                          (FStar_Extraction_ML_Syntax.MLC_Unit
                                                          );
                                                        FStar_Extraction_ML_Syntax.mlty
                                                          = uu____4655;
                                                        FStar_Extraction_ML_Syntax.loc
                                                          = uu____4656;_}::[])
                                               ->
                                               FStar_All.pipe_right
                                                 (FStar_Extraction_ML_Syntax.MLE_App
                                                    ((let uu___144_4660 =
                                                        head3 in
                                                      {
                                                        FStar_Extraction_ML_Syntax.expr
                                                          =
                                                          (uu___144_4660.FStar_Extraction_ML_Syntax.expr);
                                                        FStar_Extraction_ML_Syntax.mlty
                                                          =
                                                          (FStar_Extraction_ML_Syntax.MLTY_Fun
                                                             (FStar_Extraction_ML_Syntax.ml_unit_ty,
                                                               FStar_Extraction_ML_Syntax.E_PURE,
                                                               t2));
                                                        FStar_Extraction_ML_Syntax.loc
                                                          =
                                                          (uu___144_4660.FStar_Extraction_ML_Syntax.loc)
                                                      }),
                                                      [FStar_Extraction_ML_Syntax.ml_unit]))
                                                 (FStar_Extraction_ML_Syntax.with_ty
                                                    t2)
                                           | uu____4661 ->
                                               failwith
                                                 "Impossible: Unexpected head term" in
                                         (head3, t2, rest))
                                  else err_uninst g head2 (vars, t1) top in
                            (match uu____4542 with
                             | (head_ml1,head_t,args1) ->
                                 (match args1 with
                                  | [] ->
                                      let uu____4699 =
                                        maybe_eta_data_and_project_record g
                                          qual head_t head_ml1 in
                                      (uu____4699,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        head_t)
                                  | uu____4700 ->
                                      extract_app_maybe_projector qual
                                        head_ml1
                                        (FStar_Extraction_ML_Syntax.E_PURE,
                                          head_t) args1)))
                   | FStar_Syntax_Syntax.Tm_fvar uu____4706 ->
                       let uu____4707 =
                         let uu____4714 =
                           FStar_Extraction_ML_UEnv.lookup_term g head2 in
                         match uu____4714 with
                         | (FStar_Util.Inr (uu____4724,x1,x2,x3),q) ->
                             ((x1, x2, x3), q)
                         | uu____4749 -> failwith "FIXME Ty" in
                       (match uu____4707 with
                        | ((head_ml,(vars,t1),inst_ok),qual) ->
                            let has_typ_apps =
                              match args with
                              | (a,uu____4778)::uu____4779 -> is_type g a
                              | uu____4793 -> false in
                            let uu____4799 =
                              match vars with
                              | uu____4816::uu____4817 when
                                  (Prims.op_Negation has_typ_apps) && inst_ok
                                  -> (head_ml, t1, args)
                              | uu____4824 ->
                                  let n1 = FStar_List.length vars in
                                  if n1 <= (FStar_List.length args)
                                  then
                                    let uu____4844 =
                                      FStar_Util.first_N n1 args in
                                    (match uu____4844 with
                                     | (prefix1,rest) ->
                                         let prefixAsMLTypes =
                                           FStar_List.map
                                             (fun uu____4900  ->
                                                match uu____4900 with
                                                | (x,uu____4904) ->
                                                    term_as_mlty g x) prefix1 in
                                         let t2 =
                                           instantiate (vars, t1)
                                             prefixAsMLTypes in
                                         let head3 =
                                           match head_ml.FStar_Extraction_ML_Syntax.expr
                                           with
                                           | FStar_Extraction_ML_Syntax.MLE_Name
                                               uu____4907 ->
                                               let uu___143_4908 = head_ml in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (uu___143_4908.FStar_Extraction_ML_Syntax.expr);
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   = t2;
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___143_4908.FStar_Extraction_ML_Syntax.loc)
                                               }
                                           | FStar_Extraction_ML_Syntax.MLE_Var
                                               uu____4909 ->
                                               let uu___143_4910 = head_ml in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (uu___143_4910.FStar_Extraction_ML_Syntax.expr);
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   = t2;
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___143_4910.FStar_Extraction_ML_Syntax.loc)
                                               }
                                           | FStar_Extraction_ML_Syntax.MLE_App
                                               (head3,{
                                                        FStar_Extraction_ML_Syntax.expr
                                                          =
                                                          FStar_Extraction_ML_Syntax.MLE_Const
                                                          (FStar_Extraction_ML_Syntax.MLC_Unit
                                                          );
                                                        FStar_Extraction_ML_Syntax.mlty
                                                          = uu____4912;
                                                        FStar_Extraction_ML_Syntax.loc
                                                          = uu____4913;_}::[])
                                               ->
                                               FStar_All.pipe_right
                                                 (FStar_Extraction_ML_Syntax.MLE_App
                                                    ((let uu___144_4917 =
                                                        head3 in
                                                      {
                                                        FStar_Extraction_ML_Syntax.expr
                                                          =
                                                          (uu___144_4917.FStar_Extraction_ML_Syntax.expr);
                                                        FStar_Extraction_ML_Syntax.mlty
                                                          =
                                                          (FStar_Extraction_ML_Syntax.MLTY_Fun
                                                             (FStar_Extraction_ML_Syntax.ml_unit_ty,
                                                               FStar_Extraction_ML_Syntax.E_PURE,
                                                               t2));
                                                        FStar_Extraction_ML_Syntax.loc
                                                          =
                                                          (uu___144_4917.FStar_Extraction_ML_Syntax.loc)
                                                      }),
                                                      [FStar_Extraction_ML_Syntax.ml_unit]))
                                                 (FStar_Extraction_ML_Syntax.with_ty
                                                    t2)
                                           | uu____4918 ->
                                               failwith
                                                 "Impossible: Unexpected head term" in
                                         (head3, t2, rest))
                                  else err_uninst g head2 (vars, t1) top in
                            (match uu____4799 with
                             | (head_ml1,head_t,args1) ->
                                 (match args1 with
                                  | [] ->
                                      let uu____4956 =
                                        maybe_eta_data_and_project_record g
                                          qual head_t head_ml1 in
                                      (uu____4956,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        head_t)
                                  | uu____4957 ->
                                      extract_app_maybe_projector qual
                                        head_ml1
                                        (FStar_Extraction_ML_Syntax.E_PURE,
                                          head_t) args1)))
                   | uu____4963 ->
                       let uu____4964 = term_as_mlexpr g head2 in
                       (match uu____4964 with
                        | (head3,f,t1) ->
                            extract_app_maybe_projector None head3 (f, t1)
                              args)))
       | FStar_Syntax_Syntax.Tm_ascribed (e0,(tc,uu____4976),f) ->
           let t1 =
             match tc with
             | FStar_Util.Inl t1 -> term_as_mlty g t1
             | FStar_Util.Inr c ->
                 term_as_mlty g (FStar_Syntax_Util.comp_result c) in
           let f1 =
             match f with
             | None  -> failwith "Ascription node with an empty effect label"
             | Some l -> effect_as_etag g l in
           let uu____5030 = check_term_as_mlexpr g e0 f1 t1 in
           (match uu____5030 with | (e,t2) -> (e, f1, t2))
       | FStar_Syntax_Syntax.Tm_let ((is_rec,lbs),e') ->
           let top_level = FStar_Syntax_Syntax.is_top_level lbs in
           let uu____5051 =
             if is_rec
             then FStar_Syntax_Subst.open_let_rec lbs e'
             else
               (let uu____5059 = FStar_Syntax_Syntax.is_top_level lbs in
                if uu____5059
                then (lbs, e')
                else
                  (let lb = FStar_List.hd lbs in
                   let x =
                     let uu____5069 =
                       FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                     FStar_Syntax_Syntax.freshen_bv uu____5069 in
                   let lb1 =
                     let uu___145_5071 = lb in
                     {
                       FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                       FStar_Syntax_Syntax.lbunivs =
                         (uu___145_5071.FStar_Syntax_Syntax.lbunivs);
                       FStar_Syntax_Syntax.lbtyp =
                         (uu___145_5071.FStar_Syntax_Syntax.lbtyp);
                       FStar_Syntax_Syntax.lbeff =
                         (uu___145_5071.FStar_Syntax_Syntax.lbeff);
                       FStar_Syntax_Syntax.lbdef =
                         (uu___145_5071.FStar_Syntax_Syntax.lbdef)
                     } in
                   let e'1 =
                     FStar_Syntax_Subst.subst
                       [FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x)] e' in
                   ([lb1], e'1))) in
           (match uu____5051 with
            | (lbs1,e'1) ->
                let lbs2 =
                  if top_level
                  then
                    FStar_All.pipe_right lbs1
                      (FStar_List.map
                         (fun lb  ->
                            let tcenv =
                              let uu____5093 =
                                FStar_Ident.lid_of_path
                                  (FStar_List.append
                                     (fst
                                        g.FStar_Extraction_ML_UEnv.currentModule)
                                     [snd
                                        g.FStar_Extraction_ML_UEnv.currentModule])
                                  FStar_Range.dummyRange in
                              FStar_TypeChecker_Env.set_current_module
                                g.FStar_Extraction_ML_UEnv.tcenv uu____5093 in
                            FStar_Extraction_ML_UEnv.debug g
                              (fun uu____5098  ->
                                 FStar_Options.set_option "debug_level"
                                   (FStar_Options.List
                                      [FStar_Options.String "Norm";
                                      FStar_Options.String "Extraction"]));
                            (let lbdef =
                               let uu____5102 = FStar_Options.ml_ish () in
                               if uu____5102
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
                             let uu___146_5106 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___146_5106.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___146_5106.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___146_5106.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___146_5106.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef
                             })))
                  else lbs1 in
                let maybe_generalize uu____5120 =
                  match uu____5120 with
                  | { FStar_Syntax_Syntax.lbname = lbname_;
                      FStar_Syntax_Syntax.lbunivs = uu____5131;
                      FStar_Syntax_Syntax.lbtyp = t1;
                      FStar_Syntax_Syntax.lbeff = lbeff;
                      FStar_Syntax_Syntax.lbdef = e;_} ->
                      let f_e = effect_as_etag g lbeff in
                      let t2 = FStar_Syntax_Subst.compress t1 in
                      (match t2.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                           let uu____5174 = FStar_List.hd bs in
                           FStar_All.pipe_right uu____5174 (is_type_binder g)
                           ->
                           let uu____5181 = FStar_Syntax_Subst.open_comp bs c in
                           (match uu____5181 with
                            | (bs1,c1) ->
                                let uu____5195 =
                                  let uu____5200 =
                                    FStar_Util.prefix_until
                                      (fun x  ->
                                         let uu____5220 = is_type_binder g x in
                                         Prims.op_Negation uu____5220) bs1 in
                                  match uu____5200 with
                                  | None  ->
                                      (bs1,
                                        (FStar_Syntax_Util.comp_result c1))
                                  | Some (bs2,b,rest) ->
                                      let uu____5268 =
                                        FStar_Syntax_Util.arrow (b :: rest)
                                          c1 in
                                      (bs2, uu____5268) in
                                (match uu____5195 with
                                 | (tbinders,tbody) ->
                                     let n_tbinders =
                                       FStar_List.length tbinders in
                                     let e1 =
                                       let uu____5298 = normalize_abs e in
                                       FStar_All.pipe_right uu____5298
                                         FStar_Syntax_Util.unmeta in
                                     (match e1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Tm_abs
                                          (bs2,body,copt) ->
                                          let uu____5333 =
                                            FStar_Syntax_Subst.open_term bs2
                                              body in
                                          (match uu____5333 with
                                           | (bs3,body1) ->
                                               if
                                                 n_tbinders <=
                                                   (FStar_List.length bs3)
                                               then
                                                 let uu____5363 =
                                                   FStar_Util.first_N
                                                     n_tbinders bs3 in
                                                 (match uu____5363 with
                                                  | (targs,rest_args) ->
                                                      let expected_source_ty
                                                        =
                                                        let s =
                                                          FStar_List.map2
                                                            (fun uu____5413 
                                                               ->
                                                               fun uu____5414
                                                                  ->
                                                                 match 
                                                                   (uu____5413,
                                                                    uu____5414)
                                                                 with
                                                                 | ((x,uu____5424),
                                                                    (y,uu____5426))
                                                                    ->
                                                                    let uu____5431
                                                                    =
                                                                    let uu____5436
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    y in
                                                                    (x,
                                                                    uu____5436) in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____5431)
                                                            tbinders targs in
                                                        FStar_Syntax_Subst.subst
                                                          s tbody in
                                                      let env =
                                                        FStar_List.fold_left
                                                          (fun env  ->
                                                             fun uu____5445 
                                                               ->
                                                               match uu____5445
                                                               with
                                                               | (a,uu____5449)
                                                                   ->
                                                                   FStar_Extraction_ML_UEnv.extend_ty
                                                                    env a
                                                                    None) g
                                                          targs in
                                                      let expected_t =
                                                        term_as_mlty env
                                                          expected_source_ty in
                                                      let polytype =
                                                        let uu____5457 =
                                                          FStar_All.pipe_right
                                                            targs
                                                            (FStar_List.map
                                                               (fun
                                                                  uu____5474 
                                                                  ->
                                                                  match uu____5474
                                                                  with
                                                                  | (x,uu____5480)
                                                                    ->
                                                                    FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                                    x)) in
                                                        (uu____5457,
                                                          expected_t) in
                                                      let add_unit =
                                                        match rest_args with
                                                        | [] ->
                                                            let uu____5487 =
                                                              is_fstar_value
                                                                body1 in
                                                            Prims.op_Negation
                                                              uu____5487
                                                        | uu____5488 -> false in
                                                      let rest_args1 =
                                                        if add_unit
                                                        then unit_binder ::
                                                          rest_args
                                                        else rest_args in
                                                      let body2 =
                                                        match rest_args1 with
                                                        | [] -> body1
                                                        | uu____5497 ->
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
                                          uu____5541 ->
                                          let env =
                                            FStar_List.fold_left
                                              (fun env  ->
                                                 fun uu____5554  ->
                                                   match uu____5554 with
                                                   | (a,uu____5558) ->
                                                       FStar_Extraction_ML_UEnv.extend_ty
                                                         env a None) g
                                              tbinders in
                                          let expected_t =
                                            term_as_mlty env tbody in
                                          let polytype =
                                            let uu____5566 =
                                              FStar_All.pipe_right tbinders
                                                (FStar_List.map
                                                   (fun uu____5580  ->
                                                      match uu____5580 with
                                                      | (x,uu____5586) ->
                                                          FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                            x)) in
                                            (uu____5566, expected_t) in
                                          let args =
                                            FStar_All.pipe_right tbinders
                                              (FStar_List.map
                                                 (fun uu____5599  ->
                                                    match uu____5599 with
                                                    | (bv,uu____5603) ->
                                                        let uu____5604 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            bv in
                                                        FStar_All.pipe_right
                                                          uu____5604
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
                                          uu____5638 ->
                                          let env =
                                            FStar_List.fold_left
                                              (fun env  ->
                                                 fun uu____5647  ->
                                                   match uu____5647 with
                                                   | (a,uu____5651) ->
                                                       FStar_Extraction_ML_UEnv.extend_ty
                                                         env a None) g
                                              tbinders in
                                          let expected_t =
                                            term_as_mlty env tbody in
                                          let polytype =
                                            let uu____5659 =
                                              FStar_All.pipe_right tbinders
                                                (FStar_List.map
                                                   (fun uu____5673  ->
                                                      match uu____5673 with
                                                      | (x,uu____5679) ->
                                                          FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                            x)) in
                                            (uu____5659, expected_t) in
                                          let args =
                                            FStar_All.pipe_right tbinders
                                              (FStar_List.map
                                                 (fun uu____5692  ->
                                                    match uu____5692 with
                                                    | (bv,uu____5696) ->
                                                        let uu____5697 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            bv in
                                                        FStar_All.pipe_right
                                                          uu____5697
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
                                          uu____5731 ->
                                          let env =
                                            FStar_List.fold_left
                                              (fun env  ->
                                                 fun uu____5740  ->
                                                   match uu____5740 with
                                                   | (a,uu____5744) ->
                                                       FStar_Extraction_ML_UEnv.extend_ty
                                                         env a None) g
                                              tbinders in
                                          let expected_t =
                                            term_as_mlty env tbody in
                                          let polytype =
                                            let uu____5752 =
                                              FStar_All.pipe_right tbinders
                                                (FStar_List.map
                                                   (fun uu____5766  ->
                                                      match uu____5766 with
                                                      | (x,uu____5772) ->
                                                          FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                            x)) in
                                            (uu____5752, expected_t) in
                                          let args =
                                            FStar_All.pipe_right tbinders
                                              (FStar_List.map
                                                 (fun uu____5785  ->
                                                    match uu____5785 with
                                                    | (bv,uu____5789) ->
                                                        let uu____5790 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            bv in
                                                        FStar_All.pipe_right
                                                          uu____5790
                                                          FStar_Syntax_Syntax.as_arg)) in
                                          let e2 =
                                            FStar_Syntax_Syntax.mk
                                              (FStar_Syntax_Syntax.Tm_app
                                                 (e1, args)) None
                                              e1.FStar_Syntax_Syntax.pos in
                                          (lbname_, f_e,
                                            (t2, (tbinders, polytype)),
                                            false, e2)
                                      | uu____5824 ->
                                          err_value_restriction e1)))
                       | uu____5834 ->
                           let expected_t = term_as_mlty g t2 in
                           (lbname_, f_e, (t2, ([], ([], expected_t))),
                             false, e)) in
                let check_lb env uu____5891 =
                  match uu____5891 with
                  | (nm,(lbname,f,(t1,(targs,polytype)),add_unit,e)) ->
                      let env1 =
                        FStar_List.fold_left
                          (fun env1  ->
                             fun uu____5966  ->
                               match uu____5966 with
                               | (a,uu____5970) ->
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
                      let uu____5973 =
                        check_term_as_mlexpr env1 e f expected_t in
                      (match uu____5973 with
                       | (e1,uu____5979) ->
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
                let uu____6014 =
                  FStar_List.fold_right
                    (fun lb  ->
                       fun uu____6068  ->
                         match uu____6068 with
                         | (env,lbs4) ->
                             let uu____6132 = lb in
                             (match uu____6132 with
                              | (lbname,uu____6157,(t1,(uu____6159,polytype)),add_unit,uu____6162)
                                  ->
                                  let uu____6169 =
                                    FStar_Extraction_ML_UEnv.extend_lb env
                                      lbname t1 polytype add_unit true in
                                  (match uu____6169 with
                                   | (env1,nm) -> (env1, ((nm, lb) :: lbs4)))))
                    lbs3 (g, []) in
                (match uu____6014 with
                 | (env_body,lbs4) ->
                     let env_def = if is_rec then env_body else g in
                     let lbs5 =
                       FStar_All.pipe_right lbs4
                         (FStar_List.map (check_lb env_def)) in
                     let e'_rng = e'1.FStar_Syntax_Syntax.pos in
                     let uu____6312 = term_as_mlexpr env_body e'1 in
                     (match uu____6312 with
                      | (e'2,f',t') ->
                          let f =
                            let uu____6323 =
                              let uu____6325 =
                                FStar_List.map FStar_Pervasives.fst lbs5 in
                              f' :: uu____6325 in
                            FStar_Extraction_ML_Util.join_l e'_rng uu____6323 in
                          let is_rec1 =
                            if is_rec = true
                            then FStar_Extraction_ML_Syntax.Rec
                            else FStar_Extraction_ML_Syntax.NonRec in
                          let uu____6331 =
                            let uu____6332 =
                              let uu____6333 =
                                let uu____6334 =
                                  FStar_List.map FStar_Pervasives.snd lbs5 in
                                (is_rec1, [], uu____6334) in
                              mk_MLE_Let top_level uu____6333 e'2 in
                            let uu____6340 =
                              FStar_Extraction_ML_Util.mlloc_of_range
                                t.FStar_Syntax_Syntax.pos in
                            FStar_Extraction_ML_Syntax.with_ty_loc t'
                              uu____6332 uu____6340 in
                          (uu____6331, f, t'))))
       | FStar_Syntax_Syntax.Tm_match (scrutinee,pats) ->
           let uu____6367 = term_as_mlexpr g scrutinee in
           (match uu____6367 with
            | (e,f_e,t_e) ->
                let uu____6377 = check_pats_for_ite pats in
                (match uu____6377 with
                 | (b,then_e,else_e) ->
                     let no_lift x t1 = x in
                     if b
                     then
                       (match (then_e, else_e) with
                        | (Some then_e1,Some else_e1) ->
                            let uu____6412 = term_as_mlexpr g then_e1 in
                            (match uu____6412 with
                             | (then_mle,f_then,t_then) ->
                                 let uu____6422 = term_as_mlexpr g else_e1 in
                                 (match uu____6422 with
                                  | (else_mle,f_else,t_else) ->
                                      let uu____6432 =
                                        let uu____6439 =
                                          type_leq g t_then t_else in
                                        if uu____6439
                                        then (t_else, no_lift)
                                        else
                                          (let uu____6451 =
                                             type_leq g t_else t_then in
                                           if uu____6451
                                           then (t_then, no_lift)
                                           else
                                             (FStar_Extraction_ML_Syntax.MLTY_Top,
                                               FStar_Extraction_ML_Syntax.apply_obj_repr)) in
                                      (match uu____6432 with
                                       | (t_branch,maybe_lift1) ->
                                           let uu____6480 =
                                             let uu____6481 =
                                               let uu____6482 =
                                                 let uu____6487 =
                                                   maybe_lift1 then_mle
                                                     t_then in
                                                 let uu____6488 =
                                                   let uu____6490 =
                                                     maybe_lift1 else_mle
                                                       t_else in
                                                   Some uu____6490 in
                                                 (e, uu____6487, uu____6488) in
                                               FStar_Extraction_ML_Syntax.MLE_If
                                                 uu____6482 in
                                             FStar_All.pipe_left
                                               (FStar_Extraction_ML_Syntax.with_ty
                                                  t_branch) uu____6481 in
                                           let uu____6492 =
                                             FStar_Extraction_ML_Util.join
                                               then_e1.FStar_Syntax_Syntax.pos
                                               f_then f_else in
                                           (uu____6480, uu____6492, t_branch))))
                        | uu____6493 ->
                            failwith
                              "ITE pats matched but then and else expressions not found?")
                     else
                       (let uu____6502 =
                          FStar_All.pipe_right pats
                            (FStar_Util.fold_map
                               (fun compat  ->
                                  fun br  ->
                                    let uu____6569 =
                                      FStar_Syntax_Subst.open_branch br in
                                    match uu____6569 with
                                    | (pat,when_opt,branch1) ->
                                        let uu____6597 =
                                          extract_pat g pat t_e in
                                        (match uu____6597 with
                                         | (env,p,pat_t_compat) ->
                                             let uu____6628 =
                                               match when_opt with
                                               | None  ->
                                                   (None,
                                                     FStar_Extraction_ML_Syntax.E_PURE)
                                               | Some w ->
                                                   let uu____6643 =
                                                     term_as_mlexpr env w in
                                                   (match uu____6643 with
                                                    | (w1,f_w,t_w) ->
                                                        let w2 =
                                                          maybe_coerce env w1
                                                            t_w
                                                            FStar_Extraction_ML_Syntax.ml_bool_ty in
                                                        ((Some w2), f_w)) in
                                             (match uu____6628 with
                                              | (when_opt1,f_when) ->
                                                  let uu____6671 =
                                                    term_as_mlexpr env
                                                      branch1 in
                                                  (match uu____6671 with
                                                   | (mlbranch,f_branch,t_branch)
                                                       ->
                                                       let uu____6690 =
                                                         FStar_All.pipe_right
                                                           p
                                                           (FStar_List.map
                                                              (fun uu____6731
                                                                  ->
                                                                 match uu____6731
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
                                                         uu____6690))))) true) in
                        match uu____6502 with
                        | (pat_t_compat,mlbranches) ->
                            let mlbranches1 = FStar_List.flatten mlbranches in
                            let e1 =
                              if pat_t_compat
                              then e
                              else
                                (FStar_Extraction_ML_UEnv.debug g
                                   (fun uu____6820  ->
                                      let uu____6821 =
                                        FStar_Extraction_ML_Code.string_of_mlexpr
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          e in
                                      let uu____6822 =
                                        FStar_Extraction_ML_Code.string_of_mlty
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          t_e in
                                      FStar_Util.print2
                                        "Coercing scrutinee %s from type %s because pattern type is incompatible\n"
                                        uu____6821 uu____6822);
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty t_e)
                                   (FStar_Extraction_ML_Syntax.MLE_Coerce
                                      (e, t_e,
                                        FStar_Extraction_ML_Syntax.MLTY_Top))) in
                            (match mlbranches1 with
                             | [] ->
                                 let uu____6835 =
                                   let uu____6840 =
                                     let uu____6849 =
                                       FStar_Syntax_Syntax.lid_as_fv
                                         FStar_Syntax_Const.failwith_lid
                                         FStar_Syntax_Syntax.Delta_constant
                                         None in
                                     FStar_Extraction_ML_UEnv.lookup_fv g
                                       uu____6849 in
                                   FStar_All.pipe_left FStar_Util.right
                                     uu____6840 in
                                 (match uu____6835 with
                                  | (uu____6871,fw,uu____6873,uu____6874) ->
                                      let uu____6875 =
                                        let uu____6876 =
                                          let uu____6877 =
                                            let uu____6881 =
                                              let uu____6883 =
                                                FStar_All.pipe_left
                                                  (FStar_Extraction_ML_Syntax.with_ty
                                                     FStar_Extraction_ML_Syntax.ml_string_ty)
                                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                                     (FStar_Extraction_ML_Syntax.MLC_String
                                                        "unreachable")) in
                                              [uu____6883] in
                                            (fw, uu____6881) in
                                          FStar_Extraction_ML_Syntax.MLE_App
                                            uu____6877 in
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             FStar_Extraction_ML_Syntax.ml_unit_ty)
                                          uu____6876 in
                                      (uu____6875,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        FStar_Extraction_ML_Syntax.ml_unit_ty))
                             | (uu____6885,uu____6886,(uu____6887,f_first,t_first))::rest
                                 ->
                                 let uu____6919 =
                                   FStar_List.fold_left
                                     (fun uu____6946  ->
                                        fun uu____6947  ->
                                          match (uu____6946, uu____6947) with
                                          | ((topt,f),(uu____6977,uu____6978,
                                                       (uu____6979,f_branch,t_branch)))
                                              ->
                                              let f1 =
                                                FStar_Extraction_ML_Util.join
                                                  top.FStar_Syntax_Syntax.pos
                                                  f f_branch in
                                              let topt1 =
                                                match topt with
                                                | None  -> None
                                                | Some t1 ->
                                                    let uu____7010 =
                                                      type_leq g t1 t_branch in
                                                    if uu____7010
                                                    then Some t_branch
                                                    else
                                                      (let uu____7013 =
                                                         type_leq g t_branch
                                                           t1 in
                                                       if uu____7013
                                                       then Some t1
                                                       else None) in
                                              (topt1, f1))
                                     ((Some t_first), f_first) rest in
                                 (match uu____6919 with
                                  | (topt,f_match) ->
                                      let mlbranches2 =
                                        FStar_All.pipe_right mlbranches1
                                          (FStar_List.map
                                             (fun uu____7067  ->
                                                match uu____7067 with
                                                | (p,(wopt,uu____7083),
                                                   (b1,uu____7085,t1)) ->
                                                    let b2 =
                                                      match topt with
                                                      | None  ->
                                                          FStar_Extraction_ML_Syntax.apply_obj_repr
                                                            b1 t1
                                                      | Some uu____7096 -> b1 in
                                                    (p, wopt, b2))) in
                                      let t_match =
                                        match topt with
                                        | None  ->
                                            FStar_Extraction_ML_Syntax.MLTY_Top
                                        | Some t1 -> t1 in
                                      let uu____7100 =
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             t_match)
                                          (FStar_Extraction_ML_Syntax.MLE_Match
                                             (e1, mlbranches2)) in
                                      (uu____7100, f_match, t_match)))))))
let fresh: Prims.string -> (Prims.string* Prims.int) =
  let c = FStar_Util.mk_ref (Prims.parse_int "0") in
  fun x  ->
    FStar_Util.incr c; (let uu____7118 = FStar_ST.read c in (x, uu____7118))
let ind_discriminator_body:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlmodule1
  =
  fun env  ->
    fun discName  ->
      fun constrName  ->
        let uu____7130 =
          let uu____7133 =
            FStar_TypeChecker_Env.lookup_lid
              env.FStar_Extraction_ML_UEnv.tcenv discName in
          FStar_All.pipe_left FStar_Pervasives.fst uu____7133 in
        match uu____7130 with
        | (uu____7146,fstar_disc_type) ->
            let wildcards =
              let uu____7154 =
                let uu____7155 = FStar_Syntax_Subst.compress fstar_disc_type in
                uu____7155.FStar_Syntax_Syntax.n in
              match uu____7154 with
              | FStar_Syntax_Syntax.Tm_arrow (binders,uu____7164) ->
                  let uu____7175 =
                    FStar_All.pipe_right binders
                      (FStar_List.filter
                         (fun uu___140_7193  ->
                            match uu___140_7193 with
                            | (uu____7197,Some (FStar_Syntax_Syntax.Implicit
                               uu____7198)) -> true
                            | uu____7200 -> false)) in
                  FStar_All.pipe_right uu____7175
                    (FStar_List.map
                       (fun uu____7222  ->
                          let uu____7226 = fresh "_" in
                          (uu____7226, FStar_Extraction_ML_Syntax.MLTY_Top)))
              | uu____7231 -> failwith "Discriminator must be a function" in
            let mlid = fresh "_discr_" in
            let targ = FStar_Extraction_ML_Syntax.MLTY_Top in
            let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top in
            let discrBody =
              let uu____7243 =
                let uu____7244 =
                  let uu____7250 =
                    let uu____7251 =
                      let uu____7252 =
                        let uu____7260 =
                          let uu____7261 =
                            let uu____7262 =
                              let uu____7263 =
                                FStar_Extraction_ML_Syntax.idsym mlid in
                              ([], uu____7263) in
                            FStar_Extraction_ML_Syntax.MLE_Name uu____7262 in
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty targ)
                            uu____7261 in
                        let uu____7265 =
                          let uu____7271 =
                            let uu____7276 =
                              let uu____7277 =
                                let uu____7281 =
                                  FStar_Extraction_ML_Syntax.mlpath_of_lident
                                    constrName in
                                (uu____7281,
                                  [FStar_Extraction_ML_Syntax.MLP_Wild]) in
                              FStar_Extraction_ML_Syntax.MLP_CTor uu____7277 in
                            let uu____7283 =
                              FStar_All.pipe_left
                                (FStar_Extraction_ML_Syntax.with_ty
                                   FStar_Extraction_ML_Syntax.ml_bool_ty)
                                (FStar_Extraction_ML_Syntax.MLE_Const
                                   (FStar_Extraction_ML_Syntax.MLC_Bool true)) in
                            (uu____7276, None, uu____7283) in
                          let uu____7285 =
                            let uu____7291 =
                              let uu____7296 =
                                FStar_All.pipe_left
                                  (FStar_Extraction_ML_Syntax.with_ty
                                     FStar_Extraction_ML_Syntax.ml_bool_ty)
                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                     (FStar_Extraction_ML_Syntax.MLC_Bool
                                        false)) in
                              (FStar_Extraction_ML_Syntax.MLP_Wild, None,
                                uu____7296) in
                            [uu____7291] in
                          uu____7271 :: uu____7285 in
                        (uu____7260, uu____7265) in
                      FStar_Extraction_ML_Syntax.MLE_Match uu____7252 in
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.ml_bool_ty) uu____7251 in
                  ((FStar_List.append wildcards [(mlid, targ)]), uu____7250) in
                FStar_Extraction_ML_Syntax.MLE_Fun uu____7244 in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty disc_ty) uu____7243 in
            let uu____7334 =
              let uu____7335 =
                let uu____7337 =
                  let uu____7338 =
                    FStar_Extraction_ML_UEnv.convIdent
                      discName.FStar_Ident.ident in
                  {
                    FStar_Extraction_ML_Syntax.mllb_name = uu____7338;
                    FStar_Extraction_ML_Syntax.mllb_tysc = None;
                    FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                    FStar_Extraction_ML_Syntax.mllb_def = discrBody;
                    FStar_Extraction_ML_Syntax.print_typ = false
                  } in
                [uu____7337] in
              (FStar_Extraction_ML_Syntax.NonRec, [], uu____7335) in
            FStar_Extraction_ML_Syntax.MLM_Let uu____7334