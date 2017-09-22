open Prims
exception Un_extractable
let uu___is_Un_extractable: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Un_extractable  -> true | uu____5 -> false
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
    FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option ->
      FStar_Extraction_ML_Syntax.mlty ->
        FStar_Extraction_ML_Syntax.mlty ->
          (Prims.bool,FStar_Extraction_ML_Syntax.mlexpr
                        FStar_Pervasives_Native.option)
            FStar_Pervasives_Native.tuple2
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
let record_fields:
  'Auu____65 .
    FStar_Ident.ident Prims.list ->
      'Auu____65 Prims.list ->
        (Prims.string,'Auu____65) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun fs  ->
    fun vs  ->
      FStar_List.map2 (fun f  -> fun e  -> ((f.FStar_Ident.idText), e)) fs vs
let fail: 'Auu____102 . FStar_Range.range -> Prims.string -> 'Auu____102 =
  fun r  ->
    fun msg  ->
      (let uu____112 =
         let uu____113 = FStar_Range.string_of_range r in
         FStar_Util.format2 "%s: %s\n" uu____113 msg in
       FStar_All.pipe_left FStar_Util.print_string uu____112);
      failwith msg
let err_uninst:
  'Auu____124 .
    FStar_Extraction_ML_UEnv.env ->
      FStar_Syntax_Syntax.term ->
        (Prims.string Prims.list,FStar_Extraction_ML_Syntax.mlty)
          FStar_Pervasives_Native.tuple2 ->
          FStar_Syntax_Syntax.term -> 'Auu____124
  =
  fun env  ->
    fun t  ->
      fun uu____145  ->
        fun app  ->
          match uu____145 with
          | (vars,ty) ->
              let uu____159 =
                let uu____160 = FStar_Syntax_Print.term_to_string t in
                let uu____161 =
                  FStar_All.pipe_right vars (FStar_String.concat ", ") in
                let uu____164 =
                  FStar_Extraction_ML_Code.string_of_mlty
                    env.FStar_Extraction_ML_UEnv.currentModule ty in
                let uu____165 = FStar_Syntax_Print.term_to_string app in
                FStar_Util.format4
                  "Variable %s has a polymorphic type (forall %s. %s); expected it to be fully instantiated, but got %s"
                  uu____160 uu____161 uu____164 uu____165 in
              fail t.FStar_Syntax_Syntax.pos uu____159
let err_ill_typed_application:
  'Auu____178 'Auu____179 .
    FStar_Extraction_ML_UEnv.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term,'Auu____179) FStar_Pervasives_Native.tuple2
          Prims.list -> FStar_Extraction_ML_Syntax.mlty -> 'Auu____178
  =
  fun env  ->
    fun t  ->
      fun args  ->
        fun ty  ->
          let uu____208 =
            let uu____209 = FStar_Syntax_Print.term_to_string t in
            let uu____210 =
              let uu____211 =
                FStar_All.pipe_right args
                  (FStar_List.map
                     (fun uu____229  ->
                        match uu____229 with
                        | (x,uu____235) ->
                            FStar_Syntax_Print.term_to_string x)) in
              FStar_All.pipe_right uu____211 (FStar_String.concat " ") in
            let uu____238 =
              FStar_Extraction_ML_Code.string_of_mlty
                env.FStar_Extraction_ML_UEnv.currentModule ty in
            FStar_Util.format3
              "Ill-typed application: application is %s \n remaining args are %s\nml type of head is %s\n"
              uu____209 uu____210 uu____238 in
          fail t.FStar_Syntax_Syntax.pos uu____208
let err_value_restriction:
  'Auu____243 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> 'Auu____243
  =
  fun t  ->
    let uu____252 =
      let uu____253 = FStar_Syntax_Print.tag_of_term t in
      let uu____254 = FStar_Syntax_Print.term_to_string t in
      FStar_Util.format2
        "Refusing to generalize because of the value restriction: (%s) %s"
        uu____253 uu____254 in
    fail t.FStar_Syntax_Syntax.pos uu____252
let err_unexpected_eff:
  'Auu____263 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Extraction_ML_Syntax.e_tag ->
        FStar_Extraction_ML_Syntax.e_tag -> 'Auu____263
  =
  fun t  ->
    fun f0  ->
      fun f1  ->
        let uu____280 =
          let uu____281 = FStar_Syntax_Print.term_to_string t in
          FStar_Util.format3
            "for expression %s, Expected effect %s; got effect %s" uu____281
            (FStar_Extraction_ML_Util.eff_to_string f0)
            (FStar_Extraction_ML_Util.eff_to_string f1) in
        fail t.FStar_Syntax_Syntax.pos uu____280
let effect_as_etag:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Ident.lident -> FStar_Extraction_ML_Syntax.e_tag
  =
  let cache = FStar_Util.smap_create (Prims.parse_int "20") in
  let rec delta_norm_eff g l =
    let uu____298 = FStar_Util.smap_try_find cache l.FStar_Ident.str in
    match uu____298 with
    | FStar_Pervasives_Native.Some l1 -> l1
    | FStar_Pervasives_Native.None  ->
        let res =
          let uu____303 =
            FStar_TypeChecker_Env.lookup_effect_abbrev
              g.FStar_Extraction_ML_UEnv.tcenv [FStar_Syntax_Syntax.U_zero] l in
          match uu____303 with
          | FStar_Pervasives_Native.None  -> l
          | FStar_Pervasives_Native.Some (uu____314,c) ->
              delta_norm_eff g (FStar_Syntax_Util.comp_effect_name c) in
        (FStar_Util.smap_add cache l.FStar_Ident.str res; res) in
  fun g  ->
    fun l  ->
      let l1 = delta_norm_eff g l in
      if FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid
      then FStar_Extraction_ML_Syntax.E_PURE
      else
        if FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GHOST_lid
        then FStar_Extraction_ML_Syntax.E_GHOST
        else
          (let ed_opt =
             FStar_TypeChecker_Env.effect_decl_opt
               g.FStar_Extraction_ML_UEnv.tcenv l1 in
           match ed_opt with
           | FStar_Pervasives_Native.Some (ed,qualifiers) ->
               let uu____347 =
                 FStar_All.pipe_right qualifiers
                   (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
               if uu____347
               then FStar_Extraction_ML_Syntax.E_PURE
               else FStar_Extraction_ML_Syntax.E_IMPURE
           | FStar_Pervasives_Native.None  ->
               FStar_Extraction_ML_Syntax.E_IMPURE)
let rec is_arity:
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t in
      let uu____366 =
        let uu____367 = FStar_Syntax_Subst.compress t1 in
        uu____367.FStar_Syntax_Syntax.n in
      match uu____366 with
      | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____370 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_ascribed uu____395 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_meta uu____422 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_uvar uu____429 -> false
      | FStar_Syntax_Syntax.Tm_constant uu____446 -> false
      | FStar_Syntax_Syntax.Tm_name uu____447 -> false
      | FStar_Syntax_Syntax.Tm_bvar uu____448 -> false
      | FStar_Syntax_Syntax.Tm_type uu____449 -> true
      | FStar_Syntax_Syntax.Tm_arrow (uu____450,c) ->
          is_arity env (FStar_Syntax_Util.comp_result c)
      | FStar_Syntax_Syntax.Tm_fvar uu____468 ->
          let t2 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Normalize.AllowUnboundUniverses;
              FStar_TypeChecker_Normalize.EraseUniverses;
              FStar_TypeChecker_Normalize.UnfoldUntil
                FStar_Syntax_Syntax.Delta_constant]
              env.FStar_Extraction_ML_UEnv.tcenv t1 in
          let uu____470 =
            let uu____471 = FStar_Syntax_Subst.compress t2 in
            uu____471.FStar_Syntax_Syntax.n in
          (match uu____470 with
           | FStar_Syntax_Syntax.Tm_fvar uu____474 -> false
           | uu____475 -> is_arity env t2)
      | FStar_Syntax_Syntax.Tm_app uu____476 ->
          let uu____491 = FStar_Syntax_Util.head_and_args t1 in
          (match uu____491 with | (head1,uu____507) -> is_arity env head1)
      | FStar_Syntax_Syntax.Tm_uinst (head1,uu____529) -> is_arity env head1
      | FStar_Syntax_Syntax.Tm_refine (x,uu____535) ->
          is_arity env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_abs (uu____540,body,uu____542) ->
          is_arity env body
      | FStar_Syntax_Syntax.Tm_let (uu____563,body) -> is_arity env body
      | FStar_Syntax_Syntax.Tm_match (uu____581,branches) ->
          (match branches with
           | (uu____619,uu____620,e)::uu____622 -> is_arity env e
           | uu____669 -> false)
let rec is_type_aux:
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Subst.compress t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____695 ->
          let uu____720 =
            let uu____721 = FStar_Syntax_Print.tag_of_term t1 in
            FStar_Util.format1 "Impossible: %s" uu____721 in
          failwith uu____720
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____722 =
            let uu____723 = FStar_Syntax_Print.tag_of_term t1 in
            FStar_Util.format1 "Impossible: %s" uu____723 in
          failwith uu____722
      | FStar_Syntax_Syntax.Tm_constant uu____724 -> false
      | FStar_Syntax_Syntax.Tm_type uu____725 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____726 -> true
      | FStar_Syntax_Syntax.Tm_arrow uu____733 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.failwith_lid ->
          false
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Extraction_ML_UEnv.is_type_name env fv
      | FStar_Syntax_Syntax.Tm_uvar (uu____748,t2) -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_bvar
          { FStar_Syntax_Syntax.ppname = uu____774;
            FStar_Syntax_Syntax.index = uu____775;
            FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_name
          { FStar_Syntax_Syntax.ppname = uu____779;
            FStar_Syntax_Syntax.index = uu____780;
            FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____785,uu____786) ->
          is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____828) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____835) ->
          let uu____856 = FStar_Syntax_Subst.open_term bs body in
          (match uu____856 with | (uu____861,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
          let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
          let uu____878 =
            let uu____883 =
              let uu____884 = FStar_Syntax_Syntax.mk_binder x in [uu____884] in
            FStar_Syntax_Subst.open_term uu____883 body in
          (match uu____878 with | (uu____885,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_let ((uu____887,lbs),body) ->
          let uu____904 = FStar_Syntax_Subst.open_let_rec lbs body in
          (match uu____904 with | (uu____911,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_match (uu____917,branches) ->
          (match branches with
           | b::uu____956 ->
               let uu____1001 = FStar_Syntax_Subst.open_branch b in
               (match uu____1001 with
                | (uu____1002,uu____1003,e) -> is_type_aux env e)
           | uu____1021 -> false)
      | FStar_Syntax_Syntax.Tm_meta (t2,uu____1039) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_app (head1,uu____1045) ->
          is_type_aux env head1
let is_type:
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      FStar_Extraction_ML_UEnv.debug env
        (fun uu____1078  ->
           let uu____1079 = FStar_Syntax_Print.tag_of_term t in
           let uu____1080 = FStar_Syntax_Print.term_to_string t in
           FStar_Util.print2 "checking is_type (%s) %s\n" uu____1079
             uu____1080);
      (let b = is_type_aux env t in
       FStar_Extraction_ML_UEnv.debug env
         (fun uu____1086  ->
            if b
            then
              let uu____1087 = FStar_Syntax_Print.term_to_string t in
              let uu____1088 = FStar_Syntax_Print.tag_of_term t in
              FStar_Util.print2 "is_type %s (%s)\n" uu____1087 uu____1088
            else
              (let uu____1090 = FStar_Syntax_Print.term_to_string t in
               let uu____1091 = FStar_Syntax_Print.tag_of_term t in
               FStar_Util.print2 "not a type %s (%s)\n" uu____1090 uu____1091));
       b)
let is_type_binder:
  'Auu____1098 .
    FStar_Extraction_ML_UEnv.env ->
      (FStar_Syntax_Syntax.bv,'Auu____1098) FStar_Pervasives_Native.tuple2 ->
        Prims.bool
  =
  fun env  ->
    fun x  ->
      is_arity env (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
let is_constructor: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1119 =
      let uu____1120 = FStar_Syntax_Subst.compress t in
      uu____1120.FStar_Syntax_Syntax.n in
    match uu____1119 with
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____1123;
          FStar_Syntax_Syntax.fv_delta = uu____1124;
          FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
            (FStar_Syntax_Syntax.Data_ctor );_}
        -> true
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____1125;
          FStar_Syntax_Syntax.fv_delta = uu____1126;
          FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
            (FStar_Syntax_Syntax.Record_ctor uu____1127);_}
        -> true
    | uu____1134 -> false
let rec is_fstar_value: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1139 =
      let uu____1140 = FStar_Syntax_Subst.compress t in
      uu____1140.FStar_Syntax_Syntax.n in
    match uu____1139 with
    | FStar_Syntax_Syntax.Tm_constant uu____1143 -> true
    | FStar_Syntax_Syntax.Tm_bvar uu____1144 -> true
    | FStar_Syntax_Syntax.Tm_fvar uu____1145 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____1146 -> true
    | FStar_Syntax_Syntax.Tm_app (head1,args) ->
        let uu____1185 = is_constructor head1 in
        if uu____1185
        then
          FStar_All.pipe_right args
            (FStar_List.for_all
               (fun uu____1201  ->
                  match uu____1201 with
                  | (te,uu____1207) -> is_fstar_value te))
        else false
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____1210) -> is_fstar_value t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____1216,uu____1217) ->
        is_fstar_value t1
    | uu____1258 -> false
let rec is_ml_value: FStar_Extraction_ML_Syntax.mlexpr -> Prims.bool =
  fun e  ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_Const uu____1263 -> true
    | FStar_Extraction_ML_Syntax.MLE_Var uu____1264 -> true
    | FStar_Extraction_ML_Syntax.MLE_Name uu____1265 -> true
    | FStar_Extraction_ML_Syntax.MLE_Fun uu____1266 -> true
    | FStar_Extraction_ML_Syntax.MLE_CTor (uu____1277,exps) ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Tuple exps ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Record (uu____1286,fields) ->
        FStar_Util.for_all
          (fun uu____1311  ->
             match uu____1311 with | (uu____1316,e1) -> is_ml_value e1)
          fields
    | FStar_Extraction_ML_Syntax.MLE_TApp (h,uu____1319) -> is_ml_value h
    | uu____1324 -> false
let normalize_abs: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t0  ->
    let rec aux bs t copt =
      let t1 = FStar_Syntax_Subst.compress t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_abs (bs',body,copt1) ->
          aux (FStar_List.append bs bs') body copt1
      | uu____1383 ->
          let e' = FStar_Syntax_Util.unascribe t1 in
          let uu____1385 = FStar_Syntax_Util.is_fun e' in
          if uu____1385
          then aux bs e' copt
          else FStar_Syntax_Util.abs bs e' copt in
    aux [] t0 FStar_Pervasives_Native.None
let unit_binder: FStar_Syntax_Syntax.binder =
  let uu____1391 =
    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
      FStar_Syntax_Syntax.t_unit in
  FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____1391
let check_pats_for_ite:
  (FStar_Syntax_Syntax.pat,FStar_Syntax_Syntax.term
                             FStar_Pervasives_Native.option,FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.tuple3 Prims.list ->
    (Prims.bool,FStar_Syntax_Syntax.term FStar_Pervasives_Native.option,
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3
  =
  fun l  ->
    let def =
      (false, FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) in
    if (FStar_List.length l) <> (Prims.parse_int "2")
    then def
    else
      (let uu____1470 = FStar_List.hd l in
       match uu____1470 with
       | (p1,w1,e1) ->
           let uu____1504 =
             let uu____1513 = FStar_List.tl l in FStar_List.hd uu____1513 in
           (match uu____1504 with
            | (p2,w2,e2) ->
                (match (w1, w2, (p1.FStar_Syntax_Syntax.v),
                         (p2.FStar_Syntax_Syntax.v))
                 with
                 | (FStar_Pervasives_Native.None
                    ,FStar_Pervasives_Native.None
                    ,FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool
                    (true )),FStar_Syntax_Syntax.Pat_constant
                    (FStar_Const.Const_bool (false ))) ->
                     (true, (FStar_Pervasives_Native.Some e1),
                       (FStar_Pervasives_Native.Some e2))
                 | (FStar_Pervasives_Native.None
                    ,FStar_Pervasives_Native.None
                    ,FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool
                    (false )),FStar_Syntax_Syntax.Pat_constant
                    (FStar_Const.Const_bool (true ))) ->
                     (true, (FStar_Pervasives_Native.Some e2),
                       (FStar_Pervasives_Native.Some e1))
                 | uu____1587 -> def)))
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
          (FStar_Extraction_ML_Syntax.mlexpr,FStar_Extraction_ML_Syntax.e_tag,
            FStar_Extraction_ML_Syntax.mlty) FStar_Pervasives_Native.tuple3
  =
  fun g  ->
    fun e  ->
      fun ty  ->
        fun f  ->
          let e1 =
            let uu____1653 = erasable g f ty in
            if uu____1653
            then
              let uu____1654 =
                type_leq g ty FStar_Extraction_ML_Syntax.ml_unit_ty in
              (if uu____1654
               then FStar_Extraction_ML_Syntax.ml_unit
               else
                 FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty)
                   (FStar_Extraction_ML_Syntax.MLE_Coerce
                      (FStar_Extraction_ML_Syntax.ml_unit,
                        FStar_Extraction_ML_Syntax.ml_unit_ty, ty)))
            else e in
          (e1, f, ty)
let eta_expand:
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr
  =
  fun t  ->
    fun e  ->
      let uu____1665 = FStar_Extraction_ML_Util.doms_and_cod t in
      match uu____1665 with
      | (ts,r) ->
          if ts = []
          then e
          else
            (let vs = FStar_List.map (fun uu____1685  -> "a") ts in
             let vs_ts = FStar_List.zip vs ts in
             let vs_es =
               let uu____1696 = FStar_List.zip vs ts in
               FStar_List.map
                 (fun uu____1710  ->
                    match uu____1710 with
                    | (v1,t1) ->
                        FStar_Extraction_ML_Syntax.with_ty t1
                          (FStar_Extraction_ML_Syntax.MLE_Var v1)) uu____1696 in
             let body =
               FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty r)
                 (FStar_Extraction_ML_Syntax.MLE_App (e, vs_es)) in
             FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t)
               (FStar_Extraction_ML_Syntax.MLE_Fun (vs_ts, body)))
let maybe_eta_expand:
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr
  =
  fun expect  ->
    fun e  ->
      let uu____1734 =
        (FStar_Options.ml_no_eta_expand_coertions ()) ||
          (let uu____1736 = FStar_Options.codegen () in
           uu____1736 = (FStar_Pervasives_Native.Some "Kremlin")) in
      if uu____1734 then e else eta_expand expect e
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
          let uu____1759 =
            type_leq_c g (FStar_Pervasives_Native.Some e) ty1 expect in
          match uu____1759 with
          | (true ,FStar_Pervasives_Native.Some e') -> e'
          | uu____1769 ->
              (FStar_Extraction_ML_UEnv.debug g
                 (fun uu____1781  ->
                    let uu____1782 =
                      FStar_Extraction_ML_Code.string_of_mlexpr
                        g.FStar_Extraction_ML_UEnv.currentModule e in
                    let uu____1783 =
                      FStar_Extraction_ML_Code.string_of_mlty
                        g.FStar_Extraction_ML_UEnv.currentModule ty1 in
                    let uu____1784 =
                      FStar_Extraction_ML_Code.string_of_mlty
                        g.FStar_Extraction_ML_UEnv.currentModule expect in
                    FStar_Util.print3
                      "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n"
                      uu____1782 uu____1783 uu____1784);
               (let uu____1785 =
                  FStar_All.pipe_left
                    (FStar_Extraction_ML_Syntax.with_ty expect)
                    (FStar_Extraction_ML_Syntax.MLE_Coerce (e, ty1, expect)) in
                maybe_eta_expand expect uu____1785))
let bv_as_mlty:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlty
  =
  fun g  ->
    fun bv  ->
      let uu____1794 = FStar_Extraction_ML_UEnv.lookup_bv g bv in
      match uu____1794 with
      | FStar_Util.Inl (uu____1795,t) -> t
      | uu____1809 -> FStar_Extraction_ML_Syntax.MLTY_Top
let rec term_as_mlty:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlty
  =
  fun g  ->
    fun t0  ->
      let rec is_top_ty t =
        match t with
        | FStar_Extraction_ML_Syntax.MLTY_Top  -> true
        | FStar_Extraction_ML_Syntax.MLTY_Named uu____1852 ->
            let uu____1859 = FStar_Extraction_ML_Util.udelta_unfold g t in
            (match uu____1859 with
             | FStar_Pervasives_Native.None  -> false
             | FStar_Pervasives_Native.Some t1 -> is_top_ty t1)
        | uu____1863 -> false in
      let t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.Iota;
          FStar_TypeChecker_Normalize.Zeta;
          FStar_TypeChecker_Normalize.Inlining;
          FStar_TypeChecker_Normalize.EraseUniverses;
          FStar_TypeChecker_Normalize.AllowUnboundUniverses]
          g.FStar_Extraction_ML_UEnv.tcenv t0 in
      let mlt = term_as_mlty' g t in
      let uu____1866 = is_top_ty mlt in
      if uu____1866
      then
        let t1 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Normalize.Beta;
            FStar_TypeChecker_Normalize.Eager_unfolding;
            FStar_TypeChecker_Normalize.UnfoldUntil
              FStar_Syntax_Syntax.Delta_constant;
            FStar_TypeChecker_Normalize.Iota;
            FStar_TypeChecker_Normalize.Zeta;
            FStar_TypeChecker_Normalize.Inlining;
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
      | FStar_Syntax_Syntax.Tm_bvar uu____1872 ->
          let uu____1873 =
            let uu____1874 = FStar_Syntax_Print.term_to_string t1 in
            FStar_Util.format1 "Impossible: Unexpected term %s" uu____1874 in
          failwith uu____1873
      | FStar_Syntax_Syntax.Tm_delayed uu____1875 ->
          let uu____1900 =
            let uu____1901 = FStar_Syntax_Print.term_to_string t1 in
            FStar_Util.format1 "Impossible: Unexpected term %s" uu____1901 in
          failwith uu____1900
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____1902 =
            let uu____1903 = FStar_Syntax_Print.term_to_string t1 in
            FStar_Util.format1 "Impossible: Unexpected term %s" uu____1903 in
          failwith uu____1902
      | FStar_Syntax_Syntax.Tm_constant uu____1904 ->
          FStar_Extraction_ML_UEnv.unknownType
      | FStar_Syntax_Syntax.Tm_uvar uu____1905 ->
          FStar_Extraction_ML_UEnv.unknownType
      | FStar_Syntax_Syntax.Tm_meta (t2,uu____1923) -> term_as_mlty' env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____1928;
             FStar_Syntax_Syntax.index = uu____1929;
             FStar_Syntax_Syntax.sort = t2;_},uu____1931)
          -> term_as_mlty' env t2
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____1939) -> term_as_mlty' env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____1945,uu____1946) ->
          term_as_mlty' env t2
      | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
      | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv []
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____2013 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____2013 with
           | (bs1,c1) ->
               let uu____2020 = binders_as_ml_binders env bs1 in
               (match uu____2020 with
                | (mlbs,env1) ->
                    let t_ret =
                      let eff =
                        FStar_TypeChecker_Env.norm_eff_name
                          env1.FStar_Extraction_ML_UEnv.tcenv
                          (FStar_Syntax_Util.comp_effect_name c1) in
                      let uu____2047 =
                        let uu____2054 =
                          FStar_TypeChecker_Env.effect_decl_opt
                            env1.FStar_Extraction_ML_UEnv.tcenv eff in
                        FStar_Util.must uu____2054 in
                      match uu____2047 with
                      | (ed,qualifiers) ->
                          let uu____2075 =
                            FStar_All.pipe_right qualifiers
                              (FStar_List.contains
                                 FStar_Syntax_Syntax.Reifiable) in
                          if uu____2075
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
                    let uu____2082 =
                      FStar_List.fold_right
                        (fun uu____2101  ->
                           fun uu____2102  ->
                             match (uu____2101, uu____2102) with
                             | ((uu____2123,t2),(tag,t')) ->
                                 (FStar_Extraction_ML_Syntax.E_PURE,
                                   (FStar_Extraction_ML_Syntax.MLTY_Fun
                                      (t2, tag, t')))) mlbs (erase1, t_ret) in
                    (match uu____2082 with | (uu____2135,t2) -> t2)))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let res =
            let uu____2160 =
              let uu____2161 = FStar_Syntax_Util.un_uinst head1 in
              uu____2161.FStar_Syntax_Syntax.n in
            match uu____2160 with
            | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
            | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv args
            | FStar_Syntax_Syntax.Tm_app (head2,args') ->
                let uu____2188 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app
                       (head2, (FStar_List.append args' args)))
                    FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos in
                term_as_mlty' env uu____2188
            | uu____2205 -> FStar_Extraction_ML_UEnv.unknownType in
          res
      | FStar_Syntax_Syntax.Tm_abs (bs,ty,uu____2208) ->
          let uu____2229 = FStar_Syntax_Subst.open_term bs ty in
          (match uu____2229 with
           | (bs1,ty1) ->
               let uu____2236 = binders_as_ml_binders env bs1 in
               (match uu____2236 with | (bts,env1) -> term_as_mlty' env1 ty1))
      | FStar_Syntax_Syntax.Tm_type uu____2261 ->
          FStar_Extraction_ML_UEnv.unknownType
      | FStar_Syntax_Syntax.Tm_let uu____2262 ->
          FStar_Extraction_ML_UEnv.unknownType
      | FStar_Syntax_Syntax.Tm_match uu____2275 ->
          FStar_Extraction_ML_UEnv.unknownType
and arg_as_mlty:
  FStar_Extraction_ML_UEnv.env ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 -> FStar_Extraction_ML_Syntax.mlty
  =
  fun g  ->
    fun uu____2299  ->
      match uu____2299 with
      | (a,uu____2305) ->
          let uu____2306 = is_type g a in
          if uu____2306
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
        let uu____2311 =
          let uu____2324 =
            FStar_TypeChecker_Env.lookup_lid g.FStar_Extraction_ML_UEnv.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____2324 with
          | ((uu____2345,fvty),uu____2347) ->
              let fvty1 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Normalize.UnfoldUntil
                     FStar_Syntax_Syntax.Delta_constant]
                  g.FStar_Extraction_ML_UEnv.tcenv fvty in
              FStar_Syntax_Util.arrow_formals fvty1 in
        match uu____2311 with
        | (formals,uu____2354) ->
            let mlargs = FStar_List.map (arg_as_mlty g) args in
            let mlargs1 =
              let n_args = FStar_List.length args in
              if (FStar_List.length formals) > n_args
              then
                let uu____2398 = FStar_Util.first_N n_args formals in
                match uu____2398 with
                | (uu____2425,rest) ->
                    let uu____2451 =
                      FStar_List.map
                        (fun uu____2459  ->
                           FStar_Extraction_ML_UEnv.erasedContent) rest in
                    FStar_List.append mlargs uu____2451
              else mlargs in
            let nm =
              let uu____2466 =
                FStar_Extraction_ML_UEnv.maybe_mangle_type_projector g fv in
              match uu____2466 with
              | FStar_Pervasives_Native.Some p -> p
              | FStar_Pervasives_Native.None  ->
                  FStar_Extraction_ML_Syntax.mlpath_of_lident
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            FStar_Extraction_ML_Syntax.MLTY_Named (mlargs1, nm)
and binders_as_ml_binders:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.binders ->
      ((FStar_Extraction_ML_Syntax.mlident,FStar_Extraction_ML_Syntax.mlty)
         FStar_Pervasives_Native.tuple2 Prims.list,FStar_Extraction_ML_UEnv.env)
        FStar_Pervasives_Native.tuple2
  =
  fun g  ->
    fun bs  ->
      let uu____2484 =
        FStar_All.pipe_right bs
          (FStar_List.fold_left
             (fun uu____2527  ->
                fun b  ->
                  match uu____2527 with
                  | (ml_bs,env) ->
                      let uu____2567 = is_type_binder g b in
                      if uu____2567
                      then
                        let b1 = FStar_Pervasives_Native.fst b in
                        let env1 =
                          FStar_Extraction_ML_UEnv.extend_ty env b1
                            (FStar_Pervasives_Native.Some
                               FStar_Extraction_ML_Syntax.MLTY_Top) in
                        let ml_b =
                          let uu____2585 =
                            FStar_Extraction_ML_UEnv.bv_as_ml_termvar b1 in
                          (uu____2585, FStar_Extraction_ML_Syntax.ml_unit_ty) in
                        ((ml_b :: ml_bs), env1)
                      else
                        (let b1 = FStar_Pervasives_Native.fst b in
                         let t = term_as_mlty env b1.FStar_Syntax_Syntax.sort in
                         let uu____2599 =
                           FStar_Extraction_ML_UEnv.extend_bv env b1 
                             ([], t) false false false in
                         match uu____2599 with
                         | (env1,b2) ->
                             let ml_b =
                               let uu____2623 =
                                 FStar_Extraction_ML_UEnv.removeTick b2 in
                               (uu____2623, t) in
                             ((ml_b :: ml_bs), env1))) ([], g)) in
      match uu____2484 with | (ml_bs,env) -> ((FStar_List.rev ml_bs), env)
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
      | (FStar_Extraction_ML_Syntax.MLE_Seq es1,uu____2693) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (FStar_List.append es1 [e2])
      | (uu____2696,FStar_Extraction_ML_Syntax.MLE_Seq es2) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (e1 :: es2)
      | uu____2700 -> FStar_Extraction_ML_Syntax.MLE_Seq [e1; e2]
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
             | FStar_Pervasives_Native.Some ([],t) when
                 t = FStar_Extraction_ML_Syntax.ml_unit_ty ->
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
                    | uu____2732 when
                        (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
                          =
                          FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr
                        -> body.FStar_Extraction_ML_Syntax.expr
                    | uu____2733 ->
                        mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def
                          body)
             | uu____2734 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body))
        | uu____2737 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body)
let resugar_pat:
  FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option ->
    FStar_Extraction_ML_Syntax.mlpattern ->
      FStar_Extraction_ML_Syntax.mlpattern
  =
  fun q  ->
    fun p  ->
      match p with
      | FStar_Extraction_ML_Syntax.MLP_CTor (d,pats) ->
          let uu____2756 = FStar_Extraction_ML_Util.is_xtuple d in
          (match uu____2756 with
           | FStar_Pervasives_Native.Some n1 ->
               FStar_Extraction_ML_Syntax.MLP_Tuple pats
           | uu____2760 ->
               (match q with
                | FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Record_ctor (ty,fns)) ->
                    let path =
                      FStar_List.map FStar_Ident.text_of_id ty.FStar_Ident.ns in
                    let fs = record_fields fns pats in
                    FStar_Extraction_ML_Syntax.MLP_Record (path, fs)
                | uu____2787 -> p))
      | uu____2790 -> p
let rec extract_one_pat:
  Prims.bool ->
    FStar_Extraction_ML_UEnv.env ->
      FStar_Syntax_Syntax.pat ->
        FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option ->
          (FStar_Extraction_ML_UEnv.env,(FStar_Extraction_ML_Syntax.mlpattern,
                                          FStar_Extraction_ML_Syntax.mlexpr
                                            Prims.list)
                                          FStar_Pervasives_Native.tuple2
                                          FStar_Pervasives_Native.option,
            Prims.bool) FStar_Pervasives_Native.tuple3
  =
  fun imp  ->
    fun g  ->
      fun p  ->
        fun expected_topt  ->
          let ok t =
            match expected_topt with
            | FStar_Pervasives_Native.None  -> true
            | FStar_Pervasives_Native.Some t' ->
                let ok = type_leq g t t' in
                (if Prims.op_Negation ok
                 then
                   FStar_Extraction_ML_UEnv.debug g
                     (fun uu____2849  ->
                        let uu____2850 =
                          FStar_Extraction_ML_Code.string_of_mlty
                            g.FStar_Extraction_ML_UEnv.currentModule t' in
                        let uu____2851 =
                          FStar_Extraction_ML_Code.string_of_mlty
                            g.FStar_Extraction_ML_UEnv.currentModule t in
                        FStar_Util.print2
                          "Expected pattern type %s; got pattern type %s\n"
                          uu____2850 uu____2851)
                 else ();
                 ok) in
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int
              (c,FStar_Pervasives_Native.None )) ->
              let i = FStar_Const.Const_int (c, FStar_Pervasives_Native.None) in
              let x = FStar_Extraction_ML_Syntax.gensym () in
              let when_clause =
                let uu____2891 =
                  let uu____2892 =
                    let uu____2899 =
                      let uu____2902 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.ml_int_ty)
                          (FStar_Extraction_ML_Syntax.MLE_Var x) in
                      let uu____2903 =
                        let uu____2906 =
                          let uu____2907 =
                            let uu____2908 =
                              FStar_Extraction_ML_Util.mlconst_of_const'
                                p.FStar_Syntax_Syntax.p i in
                            FStar_All.pipe_left
                              (fun _0_44  ->
                                 FStar_Extraction_ML_Syntax.MLE_Const _0_44)
                              uu____2908 in
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty
                               FStar_Extraction_ML_Syntax.ml_int_ty)
                            uu____2907 in
                        [uu____2906] in
                      uu____2902 :: uu____2903 in
                    (FStar_Extraction_ML_Util.prims_op_equality, uu____2899) in
                  FStar_Extraction_ML_Syntax.MLE_App uu____2892 in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     FStar_Extraction_ML_Syntax.ml_bool_ty) uu____2891 in
              let uu____2911 = ok FStar_Extraction_ML_Syntax.ml_int_ty in
              (g,
                (FStar_Pervasives_Native.Some
                   ((FStar_Extraction_ML_Syntax.MLP_Var x), [when_clause])),
                uu____2911)
          | FStar_Syntax_Syntax.Pat_constant s ->
              let t =
                FStar_TypeChecker_TcTerm.tc_constant FStar_Range.dummyRange s in
              let mlty = term_as_mlty g t in
              let uu____2931 =
                let uu____2940 =
                  let uu____2947 =
                    let uu____2948 =
                      FStar_Extraction_ML_Util.mlconst_of_const'
                        p.FStar_Syntax_Syntax.p s in
                    FStar_Extraction_ML_Syntax.MLP_Const uu____2948 in
                  (uu____2947, []) in
                FStar_Pervasives_Native.Some uu____2940 in
              let uu____2957 = ok mlty in (g, uu____2931, uu____2957)
          | FStar_Syntax_Syntax.Pat_var x ->
              let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort in
              let uu____2968 =
                FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false false
                  imp in
              (match uu____2968 with
               | (g1,x1) ->
                   let uu____2991 = ok mlty in
                   (g1,
                     (if imp
                      then FStar_Pervasives_Native.None
                      else
                        FStar_Pervasives_Native.Some
                          ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                     uu____2991))
          | FStar_Syntax_Syntax.Pat_wild x ->
              let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort in
              let uu____3025 =
                FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false false
                  imp in
              (match uu____3025 with
               | (g1,x1) ->
                   let uu____3048 = ok mlty in
                   (g1,
                     (if imp
                      then FStar_Pervasives_Native.None
                      else
                        FStar_Pervasives_Native.Some
                          ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                     uu____3048))
          | FStar_Syntax_Syntax.Pat_dot_term uu____3080 ->
              (g, FStar_Pervasives_Native.None, true)
          | FStar_Syntax_Syntax.Pat_cons (f,pats) ->
              let uu____3119 =
                let uu____3124 = FStar_Extraction_ML_UEnv.lookup_fv g f in
                match uu____3124 with
                | FStar_Util.Inr
                    (uu____3129,{
                                  FStar_Extraction_ML_Syntax.expr =
                                    FStar_Extraction_ML_Syntax.MLE_Name n1;
                                  FStar_Extraction_ML_Syntax.mlty =
                                    uu____3131;
                                  FStar_Extraction_ML_Syntax.loc = uu____3132;_},ttys,uu____3134)
                    -> (n1, ttys)
                | uu____3147 -> failwith "Expected a constructor" in
              (match uu____3119 with
               | (d,tys) ->
                   let nTyVars =
                     FStar_List.length (FStar_Pervasives_Native.fst tys) in
                   let uu____3169 = FStar_Util.first_N nTyVars pats in
                   (match uu____3169 with
                    | (tysVarPats,restPats) ->
                        let f_ty_opt =
                          try
                            let mlty_args =
                              FStar_All.pipe_right tysVarPats
                                (FStar_List.map
                                   (fun uu____3302  ->
                                      match uu____3302 with
                                      | (p1,uu____3310) ->
                                          (match p1.FStar_Syntax_Syntax.v
                                           with
                                           | FStar_Syntax_Syntax.Pat_dot_term
                                               (uu____3315,t) ->
                                               term_as_mlty g t
                                           | uu____3321 ->
                                               (FStar_Extraction_ML_UEnv.debug
                                                  g
                                                  (fun uu____3325  ->
                                                     let uu____3326 =
                                                       FStar_Syntax_Print.pat_to_string
                                                         p1 in
                                                     FStar_Util.print1
                                                       "Pattern %s is not extractable"
                                                       uu____3326);
                                                FStar_Exn.raise
                                                  Un_extractable)))) in
                            let f_ty =
                              FStar_Extraction_ML_Util.subst tys mlty_args in
                            let uu____3328 =
                              FStar_Extraction_ML_Util.uncurry_mlty_fun f_ty in
                            FStar_Pervasives_Native.Some uu____3328
                          with
                          | Un_extractable  -> FStar_Pervasives_Native.None in
                        let uu____3357 =
                          FStar_Util.fold_map
                            (fun g1  ->
                               fun uu____3393  ->
                                 match uu____3393 with
                                 | (p1,imp1) ->
                                     let uu____3412 =
                                       extract_one_pat true g1 p1
                                         FStar_Pervasives_Native.None in
                                     (match uu____3412 with
                                      | (g2,p2,uu____3441) -> (g2, p2))) g
                            tysVarPats in
                        (match uu____3357 with
                         | (g1,tyMLPats) ->
                             let uu____3502 =
                               FStar_Util.fold_map
                                 (fun uu____3566  ->
                                    fun uu____3567  ->
                                      match (uu____3566, uu____3567) with
                                      | ((g2,f_ty_opt1),(p1,imp1)) ->
                                          let uu____3660 =
                                            match f_ty_opt1 with
                                            | FStar_Pervasives_Native.Some
                                                (hd1::rest,res) ->
                                                ((FStar_Pervasives_Native.Some
                                                    (rest, res)),
                                                  (FStar_Pervasives_Native.Some
                                                     hd1))
                                            | uu____3720 ->
                                                (FStar_Pervasives_Native.None,
                                                  FStar_Pervasives_Native.None) in
                                          (match uu____3660 with
                                           | (f_ty_opt2,expected_ty) ->
                                               let uu____3791 =
                                                 extract_one_pat false g2 p1
                                                   expected_ty in
                                               (match uu____3791 with
                                                | (g3,p2,uu____3832) ->
                                                    ((g3, f_ty_opt2), p2))))
                                 (g1, f_ty_opt) restPats in
                             (match uu____3502 with
                              | ((g2,f_ty_opt1),restMLPats) ->
                                  let uu____3950 =
                                    let uu____3961 =
                                      FStar_All.pipe_right
                                        (FStar_List.append tyMLPats
                                           restMLPats)
                                        (FStar_List.collect
                                           (fun uu___146_4012  ->
                                              match uu___146_4012 with
                                              | FStar_Pervasives_Native.Some
                                                  x -> [x]
                                              | uu____4054 -> [])) in
                                    FStar_All.pipe_right uu____3961
                                      FStar_List.split in
                                  (match uu____3950 with
                                   | (mlPats,when_clauses) ->
                                       let pat_ty_compat =
                                         match f_ty_opt1 with
                                         | FStar_Pervasives_Native.Some
                                             ([],t) -> ok t
                                         | uu____4127 -> false in
                                       let uu____4136 =
                                         let uu____4145 =
                                           let uu____4152 =
                                             resugar_pat
                                               f.FStar_Syntax_Syntax.fv_qual
                                               (FStar_Extraction_ML_Syntax.MLP_CTor
                                                  (d, mlPats)) in
                                           let uu____4155 =
                                             FStar_All.pipe_right
                                               when_clauses
                                               FStar_List.flatten in
                                           (uu____4152, uu____4155) in
                                         FStar_Pervasives_Native.Some
                                           uu____4145 in
                                       (g2, uu____4136, pat_ty_compat))))))
let extract_pat:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.pat ->
      FStar_Extraction_ML_Syntax.mlty ->
        (FStar_Extraction_ML_UEnv.env,(FStar_Extraction_ML_Syntax.mlpattern,
                                        FStar_Extraction_ML_Syntax.mlexpr
                                          FStar_Pervasives_Native.option)
                                        FStar_Pervasives_Native.tuple2
                                        Prims.list,Prims.bool)
          FStar_Pervasives_Native.tuple3
  =
  fun g  ->
    fun p  ->
      fun expected_t  ->
        let extract_one_pat1 g1 p1 expected_t1 =
          let uu____4246 = extract_one_pat false g1 p1 expected_t1 in
          match uu____4246 with
          | (g2,FStar_Pervasives_Native.Some (x,v1),b) -> (g2, (x, v1), b)
          | uu____4303 -> failwith "Impossible: Unable to translate pattern" in
        let mk_when_clause whens =
          match whens with
          | [] -> FStar_Pervasives_Native.None
          | hd1::tl1 ->
              let uu____4346 =
                FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd1 tl1 in
              FStar_Pervasives_Native.Some uu____4346 in
        let uu____4347 =
          extract_one_pat1 g p (FStar_Pervasives_Native.Some expected_t) in
        match uu____4347 with
        | (g1,(p1,whens),b) ->
            let when_clause = mk_when_clause whens in
            (g1, [(p1, when_clause)], b)
let maybe_eta_data_and_project_record:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option ->
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
            | FStar_Extraction_ML_Syntax.MLTY_Fun (t0,uu____4489,t1) ->
                let x = FStar_Extraction_ML_Syntax.gensym () in
                let uu____4492 =
                  let uu____4503 =
                    let uu____4512 =
                      FStar_All.pipe_left
                        (FStar_Extraction_ML_Syntax.with_ty t0)
                        (FStar_Extraction_ML_Syntax.MLE_Var x) in
                    ((x, t0), uu____4512) in
                  uu____4503 :: more_args in
                eta_args uu____4492 t1
            | FStar_Extraction_ML_Syntax.MLTY_Named (uu____4525,uu____4526)
                -> ((FStar_List.rev more_args), t)
            | uu____4549 -> failwith "Impossible: Head type is not an arrow" in
          let as_record qual1 e =
            match ((e.FStar_Extraction_ML_Syntax.expr), qual1) with
            | (FStar_Extraction_ML_Syntax.MLE_CTor
               (uu____4577,args),FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Record_ctor (tyname,fields))) ->
                let path =
                  FStar_List.map FStar_Ident.text_of_id tyname.FStar_Ident.ns in
                let fields1 = record_fields fields args in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     e.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_Record (path, fields1))
            | uu____4609 -> e in
          let resugar_and_maybe_eta qual1 e =
            let uu____4627 = eta_args [] residualType in
            match uu____4627 with
            | (eargs,tres) ->
                (match eargs with
                 | [] ->
                     let uu____4680 = as_record qual1 e in
                     FStar_Extraction_ML_Util.resugar_exp uu____4680
                 | uu____4681 ->
                     let uu____4692 = FStar_List.unzip eargs in
                     (match uu____4692 with
                      | (binders,eargs1) ->
                          (match e.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_CTor (head1,args)
                               ->
                               let body =
                                 let uu____4734 =
                                   let uu____4735 =
                                     FStar_All.pipe_left
                                       (FStar_Extraction_ML_Syntax.with_ty
                                          tres)
                                       (FStar_Extraction_ML_Syntax.MLE_CTor
                                          (head1,
                                            (FStar_List.append args eargs1))) in
                                   FStar_All.pipe_left (as_record qual1)
                                     uu____4735 in
                                 FStar_All.pipe_left
                                   FStar_Extraction_ML_Util.resugar_exp
                                   uu____4734 in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    e.FStar_Extraction_ML_Syntax.mlty)
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    (binders, body))
                           | uu____4744 ->
                               failwith "Impossible: Not a constructor"))) in
          match ((mlAppExpr.FStar_Extraction_ML_Syntax.expr), qual) with
          | (uu____4747,FStar_Pervasives_Native.None ) -> mlAppExpr
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____4751;
                FStar_Extraction_ML_Syntax.loc = uu____4752;_},mle::args),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_projector (constrname,f))) ->
              let f1 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append constrname.FStar_Ident.ns [f]) in
              let fn = FStar_Extraction_ML_Util.mlpath_of_lid f1 in
              let proj = FStar_Extraction_ML_Syntax.MLE_Proj (mle, fn) in
              let e =
                match args with
                | [] -> proj
                | uu____4779 ->
                    let uu____4782 =
                      let uu____4789 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj in
                      (uu____4789, args) in
                    FStar_Extraction_ML_Syntax.MLE_App uu____4782 in
              FStar_Extraction_ML_Syntax.with_ty
                mlAppExpr.FStar_Extraction_ML_Syntax.mlty e
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____4793;
                     FStar_Extraction_ML_Syntax.loc = uu____4794;_},uu____4795);
                FStar_Extraction_ML_Syntax.mlty = uu____4796;
                FStar_Extraction_ML_Syntax.loc = uu____4797;_},mle::args),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_projector (constrname,f))) ->
              let f1 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append constrname.FStar_Ident.ns [f]) in
              let fn = FStar_Extraction_ML_Util.mlpath_of_lid f1 in
              let proj = FStar_Extraction_ML_Syntax.MLE_Proj (mle, fn) in
              let e =
                match args with
                | [] -> proj
                | uu____4828 ->
                    let uu____4831 =
                      let uu____4838 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj in
                      (uu____4838, args) in
                    FStar_Extraction_ML_Syntax.MLE_App uu____4831 in
              FStar_Extraction_ML_Syntax.with_ty
                mlAppExpr.FStar_Extraction_ML_Syntax.mlty e
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____4842;
                FStar_Extraction_ML_Syntax.loc = uu____4843;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____4851 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs)) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____4851
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____4855;
                FStar_Extraction_ML_Syntax.loc = uu____4856;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____4858)) ->
              let uu____4871 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs)) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____4871
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____4875;
                     FStar_Extraction_ML_Syntax.loc = uu____4876;_},uu____4877);
                FStar_Extraction_ML_Syntax.mlty = uu____4878;
                FStar_Extraction_ML_Syntax.loc = uu____4879;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____4891 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs)) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____4891
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____4895;
                     FStar_Extraction_ML_Syntax.loc = uu____4896;_},uu____4897);
                FStar_Extraction_ML_Syntax.mlty = uu____4898;
                FStar_Extraction_ML_Syntax.loc = uu____4899;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____4901)) ->
              let uu____4918 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs)) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____4918
          | (FStar_Extraction_ML_Syntax.MLE_Name
             mlp,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor
             )) ->
              let uu____4924 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, [])) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____4924
          | (FStar_Extraction_ML_Syntax.MLE_Name
             mlp,FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____4928)) ->
              let uu____4937 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, [])) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____4937
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____4941;
                FStar_Extraction_ML_Syntax.loc = uu____4942;_},uu____4943),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____4950 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, [])) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____4950
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____4954;
                FStar_Extraction_ML_Syntax.loc = uu____4955;_},uu____4956),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____4957)) ->
              let uu____4970 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, [])) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____4970
          | uu____4973 -> mlAppExpr
let maybe_downgrade_eff:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.e_tag ->
      FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.e_tag
  =
  fun g  ->
    fun f  ->
      fun t  ->
        let uu____4992 =
          (f = FStar_Extraction_ML_Syntax.E_GHOST) &&
            (type_leq g t FStar_Extraction_ML_Syntax.ml_unit_ty) in
        if uu____4992 then FStar_Extraction_ML_Syntax.E_PURE else f
let rec term_as_mlexpr:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Extraction_ML_Syntax.mlexpr,FStar_Extraction_ML_Syntax.e_tag,
        FStar_Extraction_ML_Syntax.mlty) FStar_Pervasives_Native.tuple3
  =
  fun g  ->
    fun t  ->
      let uu____5046 = term_as_mlexpr' g t in
      match uu____5046 with
      | (e,tag,ty) ->
          let tag1 = maybe_downgrade_eff g tag ty in
          (FStar_Extraction_ML_UEnv.debug g
             (fun u  ->
                let uu____5067 =
                  let uu____5068 = FStar_Syntax_Print.tag_of_term t in
                  let uu____5069 = FStar_Syntax_Print.term_to_string t in
                  let uu____5070 =
                    FStar_Extraction_ML_Code.string_of_mlty
                      g.FStar_Extraction_ML_UEnv.currentModule ty in
                  FStar_Util.format4
                    "term_as_mlexpr (%s) :  %s has ML type %s and effect %s\n"
                    uu____5068 uu____5069 uu____5070
                    (FStar_Extraction_ML_Util.eff_to_string tag1) in
                FStar_Util.print_string uu____5067);
           erase g e ty tag1)
and check_term_as_mlexpr:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Extraction_ML_Syntax.e_tag ->
        FStar_Extraction_ML_Syntax.mlty ->
          (FStar_Extraction_ML_Syntax.mlexpr,FStar_Extraction_ML_Syntax.mlty)
            FStar_Pervasives_Native.tuple2
  =
  fun g  ->
    fun t  ->
      fun f  ->
        fun ty  ->
          let uu____5079 = check_term_as_mlexpr' g t f ty in
          match uu____5079 with
          | (e,t1) ->
              let uu____5090 = erase g e t1 f in
              (match uu____5090 with | (r,uu____5102,t2) -> (r, t2))
and check_term_as_mlexpr':
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Extraction_ML_Syntax.e_tag ->
        FStar_Extraction_ML_Syntax.mlty ->
          (FStar_Extraction_ML_Syntax.mlexpr,FStar_Extraction_ML_Syntax.mlty)
            FStar_Pervasives_Native.tuple2
  =
  fun g  ->
    fun e0  ->
      fun f  ->
        fun ty  ->
          let uu____5112 = term_as_mlexpr g e0 in
          match uu____5112 with
          | (e,tag,t) ->
              let tag1 = maybe_downgrade_eff g tag t in
              if FStar_Extraction_ML_Util.eff_leq tag1 f
              then let uu____5131 = maybe_coerce g e t ty in (uu____5131, ty)
              else err_unexpected_eff e0 f tag1
and term_as_mlexpr':
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Extraction_ML_Syntax.mlexpr,FStar_Extraction_ML_Syntax.e_tag,
        FStar_Extraction_ML_Syntax.mlty) FStar_Pervasives_Native.tuple3
  =
  fun g  ->
    fun top  ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u  ->
           let uu____5149 =
             let uu____5150 =
               FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos in
             let uu____5151 = FStar_Syntax_Print.tag_of_term top in
             let uu____5152 = FStar_Syntax_Print.term_to_string top in
             FStar_Util.format3 "%s: term_as_mlexpr' (%s) :  %s \n"
               uu____5150 uu____5151 uu____5152 in
           FStar_Util.print_string uu____5149);
      (let t = FStar_Syntax_Subst.compress top in
       match t.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____5160 =
             let uu____5161 = FStar_Syntax_Print.tag_of_term t in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5161 in
           failwith uu____5160
       | FStar_Syntax_Syntax.Tm_delayed uu____5168 ->
           let uu____5193 =
             let uu____5194 = FStar_Syntax_Print.tag_of_term t in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5194 in
           failwith uu____5193
       | FStar_Syntax_Syntax.Tm_uvar uu____5201 ->
           let uu____5218 =
             let uu____5219 = FStar_Syntax_Print.tag_of_term t in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5219 in
           failwith uu____5218
       | FStar_Syntax_Syntax.Tm_bvar uu____5226 ->
           let uu____5227 =
             let uu____5228 = FStar_Syntax_Print.tag_of_term t in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5228 in
           failwith uu____5227
       | FStar_Syntax_Syntax.Tm_type uu____5235 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_refine uu____5236 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_arrow uu____5243 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Mutable_alloc ))
           ->
           let uu____5261 = term_as_mlexpr' g t1 in
           (match uu____5261 with
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
            | uu____5307 -> failwith "impossible")
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_monadic (m,uu____5322)) ->
           let t2 = FStar_Syntax_Subst.compress t1 in
           (match t2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) when
                FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname ->
                let uu____5352 =
                  let uu____5359 =
                    FStar_TypeChecker_Env.effect_decl_opt
                      g.FStar_Extraction_ML_UEnv.tcenv m in
                  FStar_Util.must uu____5359 in
                (match uu____5352 with
                 | (ed,qualifiers) ->
                     let uu____5386 =
                       let uu____5387 =
                         FStar_All.pipe_right qualifiers
                           (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
                       FStar_All.pipe_right uu____5387 Prims.op_Negation in
                     if uu____5386
                     then term_as_mlexpr' g t2
                     else
                       failwith
                         "This should not happen (should have been handled at Tm_abs level)")
            | uu____5403 -> term_as_mlexpr' g t2)
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____5405) -> term_as_mlexpr' g t1
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____5411) -> term_as_mlexpr' g t1
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____5417 =
             FStar_TypeChecker_TcTerm.type_of_tot_term
               g.FStar_Extraction_ML_UEnv.tcenv t in
           (match uu____5417 with
            | (uu____5430,ty,uu____5432) ->
                let ml_ty = term_as_mlty g ty in
                let uu____5434 =
                  let uu____5435 =
                    let uu____5436 =
                      FStar_Extraction_ML_Util.mlconst_of_const'
                        t.FStar_Syntax_Syntax.pos c in
                    FStar_All.pipe_left
                      (fun _0_45  ->
                         FStar_Extraction_ML_Syntax.MLE_Const _0_45)
                      uu____5436 in
                  FStar_Extraction_ML_Syntax.with_ty ml_ty uu____5435 in
                (uu____5434, FStar_Extraction_ML_Syntax.E_PURE, ml_ty))
       | FStar_Syntax_Syntax.Tm_name uu____5437 ->
           let uu____5438 = is_type g t in
           if uu____5438
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____5446 = FStar_Extraction_ML_UEnv.lookup_term g t in
              match uu____5446 with
              | (FStar_Util.Inl uu____5459,uu____5460) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | (FStar_Util.Inr (uu____5497,x,mltys,uu____5500),qual) ->
                  (match mltys with
                   | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                       ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | ([],t1) ->
                       let uu____5546 =
                         maybe_eta_data_and_project_record g qual t1 x in
                       (uu____5546, FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | uu____5547 -> err_uninst g t mltys t))
       | FStar_Syntax_Syntax.Tm_fvar uu____5554 ->
           let uu____5555 = is_type g t in
           if uu____5555
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____5563 = FStar_Extraction_ML_UEnv.lookup_term g t in
              match uu____5563 with
              | (FStar_Util.Inl uu____5576,uu____5577) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | (FStar_Util.Inr (uu____5614,x,mltys,uu____5617),qual) ->
                  (match mltys with
                   | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                       ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | ([],t1) ->
                       let uu____5663 =
                         maybe_eta_data_and_project_record g qual t1 x in
                       (uu____5663, FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | uu____5664 -> err_uninst g t mltys t))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,copt) ->
           let uu____5694 = FStar_Syntax_Subst.open_term bs body in
           (match uu____5694 with
            | (bs1,body1) ->
                let uu____5707 = binders_as_ml_binders g bs1 in
                (match uu____5707 with
                 | (ml_bs,env) ->
                     let body2 =
                       match copt with
                       | FStar_Pervasives_Native.Some c ->
                           let uu____5740 =
                             FStar_TypeChecker_Env.is_reifiable
                               env.FStar_Extraction_ML_UEnv.tcenv c in
                           if uu____5740
                           then
                             FStar_TypeChecker_Util.reify_body
                               env.FStar_Extraction_ML_UEnv.tcenv body1
                           else body1
                       | FStar_Pervasives_Native.None  ->
                           (FStar_Extraction_ML_UEnv.debug g
                              (fun uu____5745  ->
                                 let uu____5746 =
                                   FStar_Syntax_Print.term_to_string body1 in
                                 FStar_Util.print1
                                   "No computation type for: %s\n" uu____5746);
                            body1) in
                     let uu____5747 = term_as_mlexpr env body2 in
                     (match uu____5747 with
                      | (ml_body,f,t1) ->
                          let uu____5763 =
                            FStar_List.fold_right
                              (fun uu____5782  ->
                                 fun uu____5783  ->
                                   match (uu____5782, uu____5783) with
                                   | ((uu____5804,targ),(f1,t2)) ->
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         (FStar_Extraction_ML_Syntax.MLTY_Fun
                                            (targ, f1, t2)))) ml_bs (f, t1) in
                          (match uu____5763 with
                           | (f1,tfun) ->
                               let uu____5824 =
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty tfun)
                                   (FStar_Extraction_ML_Syntax.MLE_Fun
                                      (ml_bs, ml_body)) in
                               (uu____5824, f1, tfun)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____5831);
              FStar_Syntax_Syntax.pos = uu____5832;
              FStar_Syntax_Syntax.vars = uu____5833;_},uu____5834)
           -> failwith "Unreachable? Tm_app Const_reflect"
       | FStar_Syntax_Syntax.Tm_app (head1,uu____5862::(v1,uu____5864)::[])
           when (FStar_Syntax_Util.is_fstar_tactics_embed head1) && false ->
           let uu____5905 =
             let uu____5908 = FStar_Syntax_Print.term_to_string v1 in
             FStar_Util.format2 "Trying to extract a quotation of %s"
               uu____5908 in
           let s =
             let uu____5910 =
               let uu____5911 =
                 let uu____5912 =
                   let uu____5915 = FStar_Util.marshal v1 in
                   FStar_Util.bytes_of_string uu____5915 in
                 FStar_Extraction_ML_Syntax.MLC_Bytes uu____5912 in
               FStar_Extraction_ML_Syntax.MLE_Const uu____5911 in
             FStar_Extraction_ML_Syntax.with_ty
               FStar_Extraction_ML_Syntax.ml_string_ty uu____5910 in
           let zero1 =
             FStar_Extraction_ML_Syntax.with_ty
               FStar_Extraction_ML_Syntax.ml_int_ty
               (FStar_Extraction_ML_Syntax.MLE_Const
                  (FStar_Extraction_ML_Syntax.MLC_Int
                     ("0", FStar_Pervasives_Native.None))) in
           let term_ty =
             let uu____5930 =
               FStar_Syntax_Syntax.fvar
                 FStar_Parser_Const.fstar_syntax_syntax_term
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None in
             term_as_mlty g uu____5930 in
           let marshal_from_string =
             let string_to_term_ty =
               FStar_Extraction_ML_Syntax.MLTY_Fun
                 (FStar_Extraction_ML_Syntax.ml_string_ty,
                   FStar_Extraction_ML_Syntax.E_PURE, term_ty) in
             FStar_Extraction_ML_Syntax.with_ty string_to_term_ty
               (FStar_Extraction_ML_Syntax.MLE_Name
                  (["Marshal"], "from_string")) in
           let uu____5935 =
             FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty term_ty)
               (FStar_Extraction_ML_Syntax.MLE_App
                  (marshal_from_string, [s; zero1])) in
           (uu____5935, FStar_Extraction_ML_Syntax.E_PURE, term_ty)
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let is_total rc =
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_Tot_lid)
               ||
               (FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
                  (FStar_List.existsb
                     (fun uu___147_5967  ->
                        match uu___147_5967 with
                        | FStar_Syntax_Syntax.TOTAL  -> true
                        | uu____5968 -> false))) in
           let uu____5969 =
             let uu____5974 =
               let uu____5975 = FStar_Syntax_Subst.compress head1 in
               uu____5975.FStar_Syntax_Syntax.n in
             ((head1.FStar_Syntax_Syntax.n), uu____5974) in
           (match uu____5969 with
            | (FStar_Syntax_Syntax.Tm_uvar uu____5984,uu____5985) ->
                let t1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.Iota;
                    FStar_TypeChecker_Normalize.Zeta;
                    FStar_TypeChecker_Normalize.EraseUniverses;
                    FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                    g.FStar_Extraction_ML_UEnv.tcenv t in
                term_as_mlexpr' g t1
            | (uu____6003,FStar_Syntax_Syntax.Tm_abs
               (bs,uu____6005,FStar_Pervasives_Native.Some rc)) when
                is_total rc ->
                let t1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.Iota;
                    FStar_TypeChecker_Normalize.Zeta;
                    FStar_TypeChecker_Normalize.EraseUniverses;
                    FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                    g.FStar_Extraction_ML_UEnv.tcenv t in
                term_as_mlexpr' g t1
            | (uu____6026,FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_reify )) ->
                let e =
                  let uu____6028 = FStar_List.hd args in
                  FStar_TypeChecker_Util.reify_body_with_arg
                    g.FStar_Extraction_ML_UEnv.tcenv head1 uu____6028 in
                let tm =
                  let uu____6038 =
                    let uu____6039 = FStar_TypeChecker_Util.remove_reify e in
                    let uu____6040 = FStar_List.tl args in
                    FStar_Syntax_Syntax.mk_Tm_app uu____6039 uu____6040 in
                  uu____6038 FStar_Pervasives_Native.None
                    t.FStar_Syntax_Syntax.pos in
                term_as_mlexpr' g tm
            | uu____6049 ->
                let rec extract_app is_data uu____6094 uu____6095 restArgs =
                  match (uu____6094, uu____6095) with
                  | ((mlhead,mlargs_f),(f,t1)) ->
                      (match (restArgs, t1) with
                       | ([],uu____6185) ->
                           let evaluation_order_guaranteed =
                             (((FStar_List.length mlargs_f) =
                                 (Prims.parse_int "1"))
                                ||
                                (FStar_Extraction_ML_Util.codegen_fsharp ()))
                               ||
                               (match head1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_fvar fv ->
                                    (FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.op_And)
                                      ||
                                      (FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.op_Or)
                                | uu____6207 -> false) in
                           let uu____6208 =
                             if evaluation_order_guaranteed
                             then
                               let uu____6233 =
                                 FStar_All.pipe_right
                                   (FStar_List.rev mlargs_f)
                                   (FStar_List.map
                                      FStar_Pervasives_Native.fst) in
                               ([], uu____6233)
                             else
                               FStar_List.fold_left
                                 (fun uu____6287  ->
                                    fun uu____6288  ->
                                      match (uu____6287, uu____6288) with
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
                                             let uu____6391 =
                                               let uu____6394 =
                                                 FStar_All.pipe_left
                                                   (FStar_Extraction_ML_Syntax.with_ty
                                                      arg.FStar_Extraction_ML_Syntax.mlty)
                                                   (FStar_Extraction_ML_Syntax.MLE_Var
                                                      x) in
                                               uu____6394 :: out_args in
                                             (((x, arg) :: lbs), uu____6391)))
                                 ([], []) mlargs_f in
                           (match uu____6208 with
                            | (lbs,mlargs) ->
                                let app =
                                  let uu____6444 =
                                    FStar_All.pipe_left
                                      (FStar_Extraction_ML_Syntax.with_ty t1)
                                      (FStar_Extraction_ML_Syntax.MLE_App
                                         (mlhead, mlargs)) in
                                  FStar_All.pipe_left
                                    (maybe_eta_data_and_project_record g
                                       is_data t1) uu____6444 in
                                let l_app =
                                  FStar_List.fold_right
                                    (fun uu____6456  ->
                                       fun out  ->
                                         match uu____6456 with
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
                                                         (FStar_Pervasives_Native.Some
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
                       | ((arg,uu____6477)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                          (formal_t,f',t2)) when
                           (is_type g arg) &&
                             (type_leq g formal_t
                                FStar_Extraction_ML_Syntax.ml_unit_ty)
                           ->
                           let uu____6508 =
                             let uu____6513 =
                               FStar_Extraction_ML_Util.join
                                 arg.FStar_Syntax_Syntax.pos f f' in
                             (uu____6513, t2) in
                           extract_app is_data
                             (mlhead,
                               ((FStar_Extraction_ML_Syntax.ml_unit,
                                  FStar_Extraction_ML_Syntax.E_PURE) ::
                               mlargs_f)) uu____6508 rest
                       | ((e0,uu____6525)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                          (tExpected,f',t2)) ->
                           let r = e0.FStar_Syntax_Syntax.pos in
                           let uu____6557 = term_as_mlexpr g e0 in
                           (match uu____6557 with
                            | (e01,f0,tInferred) ->
                                let e02 =
                                  maybe_coerce g e01 tInferred tExpected in
                                let uu____6574 =
                                  let uu____6579 =
                                    FStar_Extraction_ML_Util.join_l r
                                      [f; f'; f0] in
                                  (uu____6579, t2) in
                                extract_app is_data
                                  (mlhead, ((e02, f0) :: mlargs_f))
                                  uu____6574 rest)
                       | uu____6590 ->
                           let uu____6603 =
                             FStar_Extraction_ML_Util.udelta_unfold g t1 in
                           (match uu____6603 with
                            | FStar_Pervasives_Native.Some t2 ->
                                extract_app is_data (mlhead, mlargs_f)
                                  (f, t2) restArgs
                            | FStar_Pervasives_Native.None  ->
                                err_ill_typed_application g top restArgs t1)) in
                let extract_app_maybe_projector is_data mlhead uu____6660
                  args1 =
                  match uu____6660 with
                  | (f,t1) ->
                      (match is_data with
                       | FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_projector uu____6692)
                           ->
                           let rec remove_implicits args2 f1 t2 =
                             match (args2, t2) with
                             | ((a0,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____6770))::args3,FStar_Extraction_ML_Syntax.MLTY_Fun
                                (uu____6772,f',t3)) ->
                                 let uu____6809 =
                                   FStar_Extraction_ML_Util.join
                                     a0.FStar_Syntax_Syntax.pos f1 f' in
                                 remove_implicits args3 uu____6809 t3
                             | uu____6810 -> (args2, f1, t2) in
                           let uu____6835 = remove_implicits args1 f t1 in
                           (match uu____6835 with
                            | (args2,f1,t2) ->
                                extract_app is_data (mlhead, []) (f1, t2)
                                  args2)
                       | uu____6891 ->
                           extract_app is_data (mlhead, []) (f, t1) args1) in
                let uu____6904 = is_type g t in
                if uu____6904
                then
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
                else
                  (let head2 = FStar_Syntax_Util.un_uinst head1 in
                   match head2.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_fvar fv when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.fstar_refl_embed_lid)
                         &&
                         (let uu____6921 =
                            let uu____6922 =
                              FStar_Extraction_ML_Syntax.string_of_mlpath
                                g.FStar_Extraction_ML_UEnv.currentModule in
                            uu____6922 = "FStar.Tactics.Builtins" in
                          Prims.op_Negation uu____6921)
                       ->
                       (match args with
                        | a::b::[] ->
                            term_as_mlexpr g (FStar_Pervasives_Native.fst a)
                        | uu____6963 ->
                            let uu____6972 =
                              FStar_Syntax_Print.args_to_string args in
                            failwith uu____6972)
                   | FStar_Syntax_Syntax.Tm_name uu____6979 ->
                       let uu____6980 =
                         let uu____6993 =
                           FStar_Extraction_ML_UEnv.lookup_term g head2 in
                         match uu____6993 with
                         | (FStar_Util.Inr (uu____7012,x1,x2,x3),q) ->
                             ((x1, x2, x3), q)
                         | uu____7057 -> failwith "FIXME Ty" in
                       (match uu____6980 with
                        | ((head_ml,(vars,t1),inst_ok),qual) ->
                            let has_typ_apps =
                              match args with
                              | (a,uu____7107)::uu____7108 -> is_type g a
                              | uu____7127 -> false in
                            let uu____7136 =
                              match vars with
                              | uu____7165::uu____7166 when
                                  (Prims.op_Negation has_typ_apps) && inst_ok
                                  -> (head_ml, t1, args)
                              | uu____7177 ->
                                  let n1 = FStar_List.length vars in
                                  if n1 <= (FStar_List.length args)
                                  then
                                    let uu____7205 =
                                      FStar_Util.first_N n1 args in
                                    (match uu____7205 with
                                     | (prefix1,rest) ->
                                         let prefixAsMLTypes =
                                           FStar_List.map
                                             (fun uu____7294  ->
                                                match uu____7294 with
                                                | (x,uu____7300) ->
                                                    term_as_mlty g x) prefix1 in
                                         let t2 =
                                           instantiate (vars, t1)
                                             prefixAsMLTypes in
                                         let mk_tapp e ty_args =
                                           match ty_args with
                                           | [] -> e
                                           | uu____7313 ->
                                               let uu___151_7316 = e in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (FStar_Extraction_ML_Syntax.MLE_TApp
                                                      (e, ty_args));
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   =
                                                   (uu___151_7316.FStar_Extraction_ML_Syntax.mlty);
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___151_7316.FStar_Extraction_ML_Syntax.loc)
                                               } in
                                         let head3 =
                                           match head_ml.FStar_Extraction_ML_Syntax.expr
                                           with
                                           | FStar_Extraction_ML_Syntax.MLE_Name
                                               uu____7320 ->
                                               let uu___152_7321 =
                                                 mk_tapp head_ml
                                                   prefixAsMLTypes in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (uu___152_7321.FStar_Extraction_ML_Syntax.expr);
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   = t2;
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___152_7321.FStar_Extraction_ML_Syntax.loc)
                                               }
                                           | FStar_Extraction_ML_Syntax.MLE_Var
                                               uu____7322 ->
                                               let uu___152_7323 =
                                                 mk_tapp head_ml
                                                   prefixAsMLTypes in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (uu___152_7323.FStar_Extraction_ML_Syntax.expr);
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   = t2;
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___152_7323.FStar_Extraction_ML_Syntax.loc)
                                               }
                                           | FStar_Extraction_ML_Syntax.MLE_App
                                               (head3,{
                                                        FStar_Extraction_ML_Syntax.expr
                                                          =
                                                          FStar_Extraction_ML_Syntax.MLE_Const
                                                          (FStar_Extraction_ML_Syntax.MLC_Unit
                                                          );
                                                        FStar_Extraction_ML_Syntax.mlty
                                                          = uu____7325;
                                                        FStar_Extraction_ML_Syntax.loc
                                                          = uu____7326;_}::[])
                                               ->
                                               FStar_All.pipe_right
                                                 (FStar_Extraction_ML_Syntax.MLE_App
                                                    ((let uu___153_7332 =
                                                        mk_tapp head3
                                                          prefixAsMLTypes in
                                                      {
                                                        FStar_Extraction_ML_Syntax.expr
                                                          =
                                                          (uu___153_7332.FStar_Extraction_ML_Syntax.expr);
                                                        FStar_Extraction_ML_Syntax.mlty
                                                          =
                                                          (FStar_Extraction_ML_Syntax.MLTY_Fun
                                                             (FStar_Extraction_ML_Syntax.ml_unit_ty,
                                                               FStar_Extraction_ML_Syntax.E_PURE,
                                                               t2));
                                                        FStar_Extraction_ML_Syntax.loc
                                                          =
                                                          (uu___153_7332.FStar_Extraction_ML_Syntax.loc)
                                                      }),
                                                      [FStar_Extraction_ML_Syntax.ml_unit]))
                                                 (FStar_Extraction_ML_Syntax.with_ty
                                                    t2)
                                           | uu____7333 ->
                                               failwith
                                                 "Impossible: Unexpected head term" in
                                         (head3, t2, rest))
                                  else err_uninst g head2 (vars, t1) top in
                            (match uu____7136 with
                             | (head_ml1,head_t,args1) ->
                                 (match args1 with
                                  | [] ->
                                      let uu____7394 =
                                        maybe_eta_data_and_project_record g
                                          qual head_t head_ml1 in
                                      (uu____7394,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        head_t)
                                  | uu____7395 ->
                                      extract_app_maybe_projector qual
                                        head_ml1
                                        (FStar_Extraction_ML_Syntax.E_PURE,
                                          head_t) args1)))
                   | FStar_Syntax_Syntax.Tm_fvar uu____7404 ->
                       let uu____7405 =
                         let uu____7418 =
                           FStar_Extraction_ML_UEnv.lookup_term g head2 in
                         match uu____7418 with
                         | (FStar_Util.Inr (uu____7437,x1,x2,x3),q) ->
                             ((x1, x2, x3), q)
                         | uu____7482 -> failwith "FIXME Ty" in
                       (match uu____7405 with
                        | ((head_ml,(vars,t1),inst_ok),qual) ->
                            let has_typ_apps =
                              match args with
                              | (a,uu____7532)::uu____7533 -> is_type g a
                              | uu____7552 -> false in
                            let uu____7561 =
                              match vars with
                              | uu____7590::uu____7591 when
                                  (Prims.op_Negation has_typ_apps) && inst_ok
                                  -> (head_ml, t1, args)
                              | uu____7602 ->
                                  let n1 = FStar_List.length vars in
                                  if n1 <= (FStar_List.length args)
                                  then
                                    let uu____7630 =
                                      FStar_Util.first_N n1 args in
                                    (match uu____7630 with
                                     | (prefix1,rest) ->
                                         let prefixAsMLTypes =
                                           FStar_List.map
                                             (fun uu____7719  ->
                                                match uu____7719 with
                                                | (x,uu____7725) ->
                                                    term_as_mlty g x) prefix1 in
                                         let t2 =
                                           instantiate (vars, t1)
                                             prefixAsMLTypes in
                                         let mk_tapp e ty_args =
                                           match ty_args with
                                           | [] -> e
                                           | uu____7738 ->
                                               let uu___151_7741 = e in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (FStar_Extraction_ML_Syntax.MLE_TApp
                                                      (e, ty_args));
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   =
                                                   (uu___151_7741.FStar_Extraction_ML_Syntax.mlty);
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___151_7741.FStar_Extraction_ML_Syntax.loc)
                                               } in
                                         let head3 =
                                           match head_ml.FStar_Extraction_ML_Syntax.expr
                                           with
                                           | FStar_Extraction_ML_Syntax.MLE_Name
                                               uu____7745 ->
                                               let uu___152_7746 =
                                                 mk_tapp head_ml
                                                   prefixAsMLTypes in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (uu___152_7746.FStar_Extraction_ML_Syntax.expr);
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   = t2;
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___152_7746.FStar_Extraction_ML_Syntax.loc)
                                               }
                                           | FStar_Extraction_ML_Syntax.MLE_Var
                                               uu____7747 ->
                                               let uu___152_7748 =
                                                 mk_tapp head_ml
                                                   prefixAsMLTypes in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (uu___152_7748.FStar_Extraction_ML_Syntax.expr);
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   = t2;
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___152_7748.FStar_Extraction_ML_Syntax.loc)
                                               }
                                           | FStar_Extraction_ML_Syntax.MLE_App
                                               (head3,{
                                                        FStar_Extraction_ML_Syntax.expr
                                                          =
                                                          FStar_Extraction_ML_Syntax.MLE_Const
                                                          (FStar_Extraction_ML_Syntax.MLC_Unit
                                                          );
                                                        FStar_Extraction_ML_Syntax.mlty
                                                          = uu____7750;
                                                        FStar_Extraction_ML_Syntax.loc
                                                          = uu____7751;_}::[])
                                               ->
                                               FStar_All.pipe_right
                                                 (FStar_Extraction_ML_Syntax.MLE_App
                                                    ((let uu___153_7757 =
                                                        mk_tapp head3
                                                          prefixAsMLTypes in
                                                      {
                                                        FStar_Extraction_ML_Syntax.expr
                                                          =
                                                          (uu___153_7757.FStar_Extraction_ML_Syntax.expr);
                                                        FStar_Extraction_ML_Syntax.mlty
                                                          =
                                                          (FStar_Extraction_ML_Syntax.MLTY_Fun
                                                             (FStar_Extraction_ML_Syntax.ml_unit_ty,
                                                               FStar_Extraction_ML_Syntax.E_PURE,
                                                               t2));
                                                        FStar_Extraction_ML_Syntax.loc
                                                          =
                                                          (uu___153_7757.FStar_Extraction_ML_Syntax.loc)
                                                      }),
                                                      [FStar_Extraction_ML_Syntax.ml_unit]))
                                                 (FStar_Extraction_ML_Syntax.with_ty
                                                    t2)
                                           | uu____7758 ->
                                               failwith
                                                 "Impossible: Unexpected head term" in
                                         (head3, t2, rest))
                                  else err_uninst g head2 (vars, t1) top in
                            (match uu____7561 with
                             | (head_ml1,head_t,args1) ->
                                 (match args1 with
                                  | [] ->
                                      let uu____7819 =
                                        maybe_eta_data_and_project_record g
                                          qual head_t head_ml1 in
                                      (uu____7819,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        head_t)
                                  | uu____7820 ->
                                      extract_app_maybe_projector qual
                                        head_ml1
                                        (FStar_Extraction_ML_Syntax.E_PURE,
                                          head_t) args1)))
                   | uu____7829 ->
                       let uu____7830 = term_as_mlexpr g head2 in
                       (match uu____7830 with
                        | (head3,f,t1) ->
                            extract_app_maybe_projector
                              FStar_Pervasives_Native.None head3 (f, t1) args)))
       | FStar_Syntax_Syntax.Tm_ascribed (e0,(tc,uu____7848),f) ->
           let t1 =
             match tc with
             | FStar_Util.Inl t1 -> term_as_mlty g t1
             | FStar_Util.Inr c ->
                 term_as_mlty g (FStar_Syntax_Util.comp_result c) in
           let f1 =
             match f with
             | FStar_Pervasives_Native.None  ->
                 failwith "Ascription node with an empty effect label"
             | FStar_Pervasives_Native.Some l -> effect_as_etag g l in
           let uu____7915 = check_term_as_mlexpr g e0 f1 t1 in
           (match uu____7915 with | (e,t2) -> (e, f1, t2))
       | FStar_Syntax_Syntax.Tm_let ((is_rec,lbs),e') ->
           let top_level = FStar_Syntax_Syntax.is_top_level lbs in
           let uu____7946 =
             if is_rec
             then FStar_Syntax_Subst.open_let_rec lbs e'
             else
               (let uu____7960 = FStar_Syntax_Syntax.is_top_level lbs in
                if uu____7960
                then (lbs, e')
                else
                  (let lb = FStar_List.hd lbs in
                   let x =
                     let uu____7974 =
                       FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                     FStar_Syntax_Syntax.freshen_bv uu____7974 in
                   let lb1 =
                     let uu___154_7976 = lb in
                     {
                       FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                       FStar_Syntax_Syntax.lbunivs =
                         (uu___154_7976.FStar_Syntax_Syntax.lbunivs);
                       FStar_Syntax_Syntax.lbtyp =
                         (uu___154_7976.FStar_Syntax_Syntax.lbtyp);
                       FStar_Syntax_Syntax.lbeff =
                         (uu___154_7976.FStar_Syntax_Syntax.lbeff);
                       FStar_Syntax_Syntax.lbdef =
                         (uu___154_7976.FStar_Syntax_Syntax.lbdef)
                     } in
                   let e'1 =
                     FStar_Syntax_Subst.subst
                       [FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x)] e' in
                   ([lb1], e'1))) in
           (match uu____7946 with
            | (lbs1,e'1) ->
                let lbs2 =
                  if top_level
                  then
                    FStar_All.pipe_right lbs1
                      (FStar_List.map
                         (fun lb  ->
                            let tcenv =
                              let uu____8008 =
                                FStar_Ident.lid_of_path
                                  (FStar_List.append
                                     (FStar_Pervasives_Native.fst
                                        g.FStar_Extraction_ML_UEnv.currentModule)
                                     [FStar_Pervasives_Native.snd
                                        g.FStar_Extraction_ML_UEnv.currentModule])
                                  FStar_Range.dummyRange in
                              FStar_TypeChecker_Env.set_current_module
                                g.FStar_Extraction_ML_UEnv.tcenv uu____8008 in
                            FStar_Extraction_ML_UEnv.debug g
                              (fun uu____8015  ->
                                 FStar_Options.set_option "debug_level"
                                   (FStar_Options.List
                                      [FStar_Options.String "Norm";
                                      FStar_Options.String "Extraction"]));
                            (let lbdef =
                               let uu____8019 = FStar_Options.ml_ish () in
                               if uu____8019
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
                             let uu___155_8023 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___155_8023.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___155_8023.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___155_8023.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___155_8023.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef
                             })))
                  else lbs1 in
                let maybe_generalize uu____8046 =
                  match uu____8046 with
                  | { FStar_Syntax_Syntax.lbname = lbname_;
                      FStar_Syntax_Syntax.lbunivs = uu____8066;
                      FStar_Syntax_Syntax.lbtyp = t1;
                      FStar_Syntax_Syntax.lbeff = lbeff;
                      FStar_Syntax_Syntax.lbdef = e;_} ->
                      let f_e = effect_as_etag g lbeff in
                      let t2 = FStar_Syntax_Subst.compress t1 in
                      (match t2.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                           let uu____8136 = FStar_List.hd bs in
                           FStar_All.pipe_right uu____8136 (is_type_binder g)
                           ->
                           let uu____8149 = FStar_Syntax_Subst.open_comp bs c in
                           (match uu____8149 with
                            | (bs1,c1) ->
                                let uu____8174 =
                                  let uu____8181 =
                                    FStar_Util.prefix_until
                                      (fun x  ->
                                         let uu____8217 = is_type_binder g x in
                                         Prims.op_Negation uu____8217) bs1 in
                                  match uu____8181 with
                                  | FStar_Pervasives_Native.None  ->
                                      (bs1,
                                        (FStar_Syntax_Util.comp_result c1))
                                  | FStar_Pervasives_Native.Some (bs2,b,rest)
                                      ->
                                      let uu____8305 =
                                        FStar_Syntax_Util.arrow (b :: rest)
                                          c1 in
                                      (bs2, uu____8305) in
                                (match uu____8174 with
                                 | (tbinders,tbody) ->
                                     let n_tbinders =
                                       FStar_List.length tbinders in
                                     let e1 =
                                       let uu____8350 = normalize_abs e in
                                       FStar_All.pipe_right uu____8350
                                         FStar_Syntax_Util.unmeta in
                                     (match e1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Tm_abs
                                          (bs2,body,copt) ->
                                          let uu____8392 =
                                            FStar_Syntax_Subst.open_term bs2
                                              body in
                                          (match uu____8392 with
                                           | (bs3,body1) ->
                                               if
                                                 n_tbinders <=
                                                   (FStar_List.length bs3)
                                               then
                                                 let uu____8445 =
                                                   FStar_Util.first_N
                                                     n_tbinders bs3 in
                                                 (match uu____8445 with
                                                  | (targs,rest_args) ->
                                                      let expected_source_ty
                                                        =
                                                        let s =
                                                          FStar_List.map2
                                                            (fun uu____8533 
                                                               ->
                                                               fun uu____8534
                                                                  ->
                                                                 match 
                                                                   (uu____8533,
                                                                    uu____8534)
                                                                 with
                                                                 | ((x,uu____8552),
                                                                    (y,uu____8554))
                                                                    ->
                                                                    let uu____8563
                                                                    =
                                                                    let uu____8570
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    y in
                                                                    (x,
                                                                    uu____8570) in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____8563)
                                                            tbinders targs in
                                                        FStar_Syntax_Subst.subst
                                                          s tbody in
                                                      let env =
                                                        FStar_List.fold_left
                                                          (fun env  ->
                                                             fun uu____8581 
                                                               ->
                                                               match uu____8581
                                                               with
                                                               | (a,uu____8587)
                                                                   ->
                                                                   FStar_Extraction_ML_UEnv.extend_ty
                                                                    env a
                                                                    FStar_Pervasives_Native.None)
                                                          g targs in
                                                      let expected_t =
                                                        term_as_mlty env
                                                          expected_source_ty in
                                                      let polytype =
                                                        let uu____8596 =
                                                          FStar_All.pipe_right
                                                            targs
                                                            (FStar_List.map
                                                               (fun
                                                                  uu____8614 
                                                                  ->
                                                                  match uu____8614
                                                                  with
                                                                  | (x,uu____8620)
                                                                    ->
                                                                    FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                                    x)) in
                                                        (uu____8596,
                                                          expected_t) in
                                                      let add_unit =
                                                        match rest_args with
                                                        | [] ->
                                                            let uu____8628 =
                                                              is_fstar_value
                                                                body1 in
                                                            Prims.op_Negation
                                                              uu____8628
                                                        | uu____8629 -> false in
                                                      let rest_args1 =
                                                        if add_unit
                                                        then unit_binder ::
                                                          rest_args
                                                        else rest_args in
                                                      let polytype1 =
                                                        if add_unit
                                                        then
                                                          FStar_Extraction_ML_Syntax.push_unit
                                                            polytype
                                                        else polytype in
                                                      let body2 =
                                                        FStar_Syntax_Util.abs
                                                          rest_args1 body1
                                                          copt in
                                                      (lbname_, f_e,
                                                        (t2,
                                                          (targs, polytype1)),
                                                        add_unit, body2))
                                               else
                                                 failwith
                                                   "Not enough type binders")
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          uu____8698 ->
                                          let env =
                                            FStar_List.fold_left
                                              (fun env  ->
                                                 fun uu____8715  ->
                                                   match uu____8715 with
                                                   | (a,uu____8721) ->
                                                       FStar_Extraction_ML_UEnv.extend_ty
                                                         env a
                                                         FStar_Pervasives_Native.None)
                                              g tbinders in
                                          let expected_t =
                                            term_as_mlty env tbody in
                                          let polytype =
                                            let uu____8730 =
                                              FStar_All.pipe_right tbinders
                                                (FStar_List.map
                                                   (fun uu____8742  ->
                                                      match uu____8742 with
                                                      | (x,uu____8748) ->
                                                          FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                            x)) in
                                            (uu____8730, expected_t) in
                                          let args =
                                            FStar_All.pipe_right tbinders
                                              (FStar_List.map
                                                 (fun uu____8764  ->
                                                    match uu____8764 with
                                                    | (bv,uu____8770) ->
                                                        let uu____8771 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            bv in
                                                        FStar_All.pipe_right
                                                          uu____8771
                                                          FStar_Syntax_Syntax.as_arg)) in
                                          let e2 =
                                            FStar_Syntax_Syntax.mk
                                              (FStar_Syntax_Syntax.Tm_app
                                                 (e1, args))
                                              FStar_Pervasives_Native.None
                                              e1.FStar_Syntax_Syntax.pos in
                                          (lbname_, f_e,
                                            (t2, (tbinders, polytype)),
                                            false, e2)
                                      | FStar_Syntax_Syntax.Tm_fvar
                                          uu____8813 ->
                                          let env =
                                            FStar_List.fold_left
                                              (fun env  ->
                                                 fun uu____8824  ->
                                                   match uu____8824 with
                                                   | (a,uu____8830) ->
                                                       FStar_Extraction_ML_UEnv.extend_ty
                                                         env a
                                                         FStar_Pervasives_Native.None)
                                              g tbinders in
                                          let expected_t =
                                            term_as_mlty env tbody in
                                          let polytype =
                                            let uu____8839 =
                                              FStar_All.pipe_right tbinders
                                                (FStar_List.map
                                                   (fun uu____8851  ->
                                                      match uu____8851 with
                                                      | (x,uu____8857) ->
                                                          FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                            x)) in
                                            (uu____8839, expected_t) in
                                          let args =
                                            FStar_All.pipe_right tbinders
                                              (FStar_List.map
                                                 (fun uu____8873  ->
                                                    match uu____8873 with
                                                    | (bv,uu____8879) ->
                                                        let uu____8880 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            bv in
                                                        FStar_All.pipe_right
                                                          uu____8880
                                                          FStar_Syntax_Syntax.as_arg)) in
                                          let e2 =
                                            FStar_Syntax_Syntax.mk
                                              (FStar_Syntax_Syntax.Tm_app
                                                 (e1, args))
                                              FStar_Pervasives_Native.None
                                              e1.FStar_Syntax_Syntax.pos in
                                          (lbname_, f_e,
                                            (t2, (tbinders, polytype)),
                                            false, e2)
                                      | FStar_Syntax_Syntax.Tm_name
                                          uu____8922 ->
                                          let env =
                                            FStar_List.fold_left
                                              (fun env  ->
                                                 fun uu____8933  ->
                                                   match uu____8933 with
                                                   | (a,uu____8939) ->
                                                       FStar_Extraction_ML_UEnv.extend_ty
                                                         env a
                                                         FStar_Pervasives_Native.None)
                                              g tbinders in
                                          let expected_t =
                                            term_as_mlty env tbody in
                                          let polytype =
                                            let uu____8948 =
                                              FStar_All.pipe_right tbinders
                                                (FStar_List.map
                                                   (fun uu____8960  ->
                                                      match uu____8960 with
                                                      | (x,uu____8966) ->
                                                          FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                            x)) in
                                            (uu____8948, expected_t) in
                                          let args =
                                            FStar_All.pipe_right tbinders
                                              (FStar_List.map
                                                 (fun uu____8982  ->
                                                    match uu____8982 with
                                                    | (bv,uu____8988) ->
                                                        let uu____8989 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            bv in
                                                        FStar_All.pipe_right
                                                          uu____8989
                                                          FStar_Syntax_Syntax.as_arg)) in
                                          let e2 =
                                            FStar_Syntax_Syntax.mk
                                              (FStar_Syntax_Syntax.Tm_app
                                                 (e1, args))
                                              FStar_Pervasives_Native.None
                                              e1.FStar_Syntax_Syntax.pos in
                                          (lbname_, f_e,
                                            (t2, (tbinders, polytype)),
                                            false, e2)
                                      | uu____9031 ->
                                          err_value_restriction e1)))
                       | uu____9050 ->
                           let expected_t = term_as_mlty g t2 in
                           (lbname_, f_e, (t2, ([], ([], expected_t))),
                             false, e)) in
                let check_lb env uu____9154 =
                  match uu____9154 with
                  | (nm,(lbname,f,(t1,(targs,polytype)),add_unit,e)) ->
                      let env1 =
                        FStar_List.fold_left
                          (fun env1  ->
                             fun uu____9289  ->
                               match uu____9289 with
                               | (a,uu____9295) ->
                                   FStar_Extraction_ML_UEnv.extend_ty env1 a
                                     FStar_Pervasives_Native.None) env targs in
                      let expected_t = FStar_Pervasives_Native.snd polytype in
                      let uu____9297 =
                        check_term_as_mlexpr env1 e f expected_t in
                      (match uu____9297 with
                       | (e1,uu____9307) ->
                           let f1 = maybe_downgrade_eff env1 f expected_t in
                           (f1,
                             {
                               FStar_Extraction_ML_Syntax.mllb_name = nm;
                               FStar_Extraction_ML_Syntax.mllb_tysc =
                                 (FStar_Pervasives_Native.Some polytype);
                               FStar_Extraction_ML_Syntax.mllb_add_unit =
                                 add_unit;
                               FStar_Extraction_ML_Syntax.mllb_def = e1;
                               FStar_Extraction_ML_Syntax.print_typ = true
                             })) in
                let lbs3 =
                  FStar_All.pipe_right lbs2 (FStar_List.map maybe_generalize) in
                let uu____9374 =
                  FStar_List.fold_right
                    (fun lb  ->
                       fun uu____9465  ->
                         match uu____9465 with
                         | (env,lbs4) ->
                             let uu____9590 = lb in
                             (match uu____9590 with
                              | (lbname,uu____9638,(t1,(uu____9640,polytype)),add_unit,uu____9643)
                                  ->
                                  let uu____9656 =
                                    FStar_Extraction_ML_UEnv.extend_lb env
                                      lbname t1 polytype add_unit true in
                                  (match uu____9656 with
                                   | (env1,nm) -> (env1, ((nm, lb) :: lbs4)))))
                    lbs3 (g, []) in
                (match uu____9374 with
                 | (env_body,lbs4) ->
                     let env_def = if is_rec then env_body else g in
                     let lbs5 =
                       FStar_All.pipe_right lbs4
                         (FStar_List.map (check_lb env_def)) in
                     let e'_rng = e'1.FStar_Syntax_Syntax.pos in
                     let uu____9933 = term_as_mlexpr env_body e'1 in
                     (match uu____9933 with
                      | (e'2,f',t') ->
                          let f =
                            let uu____9950 =
                              let uu____9953 =
                                FStar_List.map FStar_Pervasives_Native.fst
                                  lbs5 in
                              f' :: uu____9953 in
                            FStar_Extraction_ML_Util.join_l e'_rng uu____9950 in
                          let is_rec1 =
                            if is_rec = true
                            then FStar_Extraction_ML_Syntax.Rec
                            else FStar_Extraction_ML_Syntax.NonRec in
                          let uu____9962 =
                            let uu____9963 =
                              let uu____9964 =
                                let uu____9965 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    lbs5 in
                                (is_rec1, [], uu____9965) in
                              mk_MLE_Let top_level uu____9964 e'2 in
                            let uu____9976 =
                              FStar_Extraction_ML_Util.mlloc_of_range
                                t.FStar_Syntax_Syntax.pos in
                            FStar_Extraction_ML_Syntax.with_ty_loc t'
                              uu____9963 uu____9976 in
                          (uu____9962, f, t'))))
       | FStar_Syntax_Syntax.Tm_match (scrutinee,pats) ->
           let uu____10015 = term_as_mlexpr g scrutinee in
           (match uu____10015 with
            | (e,f_e,t_e) ->
                let uu____10031 = check_pats_for_ite pats in
                (match uu____10031 with
                 | (b,then_e,else_e) ->
                     let no_lift x t1 = x in
                     if b
                     then
                       (match (then_e, else_e) with
                        | (FStar_Pervasives_Native.Some
                           then_e1,FStar_Pervasives_Native.Some else_e1) ->
                            let uu____10088 = term_as_mlexpr g then_e1 in
                            (match uu____10088 with
                             | (then_mle,f_then,t_then) ->
                                 let uu____10104 = term_as_mlexpr g else_e1 in
                                 (match uu____10104 with
                                  | (else_mle,f_else,t_else) ->
                                      let uu____10120 =
                                        let uu____10129 =
                                          type_leq g t_then t_else in
                                        if uu____10129
                                        then (t_else, no_lift)
                                        else
                                          (let uu____10143 =
                                             type_leq g t_else t_then in
                                           if uu____10143
                                           then (t_then, no_lift)
                                           else
                                             (FStar_Extraction_ML_Syntax.MLTY_Top,
                                               FStar_Extraction_ML_Syntax.apply_obj_repr)) in
                                      (match uu____10120 with
                                       | (t_branch,maybe_lift1) ->
                                           let uu____10177 =
                                             let uu____10178 =
                                               let uu____10179 =
                                                 let uu____10188 =
                                                   maybe_lift1 then_mle
                                                     t_then in
                                                 let uu____10189 =
                                                   let uu____10192 =
                                                     maybe_lift1 else_mle
                                                       t_else in
                                                   FStar_Pervasives_Native.Some
                                                     uu____10192 in
                                                 (e, uu____10188,
                                                   uu____10189) in
                                               FStar_Extraction_ML_Syntax.MLE_If
                                                 uu____10179 in
                                             FStar_All.pipe_left
                                               (FStar_Extraction_ML_Syntax.with_ty
                                                  t_branch) uu____10178 in
                                           let uu____10195 =
                                             FStar_Extraction_ML_Util.join
                                               then_e1.FStar_Syntax_Syntax.pos
                                               f_then f_else in
                                           (uu____10177, uu____10195,
                                             t_branch))))
                        | uu____10196 ->
                            failwith
                              "ITE pats matched but then and else expressions not found?")
                     else
                       (let uu____10212 =
                          FStar_All.pipe_right pats
                            (FStar_Util.fold_map
                               (fun compat  ->
                                  fun br  ->
                                    let uu____10321 =
                                      FStar_Syntax_Subst.open_branch br in
                                    match uu____10321 with
                                    | (pat,when_opt,branch1) ->
                                        let uu____10365 =
                                          extract_pat g pat t_e in
                                        (match uu____10365 with
                                         | (env,p,pat_t_compat) ->
                                             let uu____10423 =
                                               match when_opt with
                                               | FStar_Pervasives_Native.None
                                                    ->
                                                   (FStar_Pervasives_Native.None,
                                                     FStar_Extraction_ML_Syntax.E_PURE)
                                               | FStar_Pervasives_Native.Some
                                                   w ->
                                                   let uu____10445 =
                                                     term_as_mlexpr env w in
                                                   (match uu____10445 with
                                                    | (w1,f_w,t_w) ->
                                                        let w2 =
                                                          maybe_coerce env w1
                                                            t_w
                                                            FStar_Extraction_ML_Syntax.ml_bool_ty in
                                                        ((FStar_Pervasives_Native.Some
                                                            w2), f_w)) in
                                             (match uu____10423 with
                                              | (when_opt1,f_when) ->
                                                  let uu____10494 =
                                                    term_as_mlexpr env
                                                      branch1 in
                                                  (match uu____10494 with
                                                   | (mlbranch,f_branch,t_branch)
                                                       ->
                                                       let uu____10528 =
                                                         FStar_All.pipe_right
                                                           p
                                                           (FStar_List.map
                                                              (fun
                                                                 uu____10605 
                                                                 ->
                                                                 match uu____10605
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
                                                         uu____10528)))))
                               true) in
                        match uu____10212 with
                        | (pat_t_compat,mlbranches) ->
                            let mlbranches1 = FStar_List.flatten mlbranches in
                            let e1 =
                              if pat_t_compat
                              then e
                              else
                                (FStar_Extraction_ML_UEnv.debug g
                                   (fun uu____10770  ->
                                      let uu____10771 =
                                        FStar_Extraction_ML_Code.string_of_mlexpr
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          e in
                                      let uu____10772 =
                                        FStar_Extraction_ML_Code.string_of_mlty
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          t_e in
                                      FStar_Util.print2
                                        "Coercing scrutinee %s from type %s because pattern type is incompatible\n"
                                        uu____10771 uu____10772);
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty t_e)
                                   (FStar_Extraction_ML_Syntax.MLE_Coerce
                                      (e, t_e,
                                        FStar_Extraction_ML_Syntax.MLTY_Top))) in
                            (match mlbranches1 with
                             | [] ->
                                 let uu____10797 =
                                   let uu____10806 =
                                     let uu____10823 =
                                       FStar_Syntax_Syntax.lid_as_fv
                                         FStar_Parser_Const.failwith_lid
                                         FStar_Syntax_Syntax.Delta_constant
                                         FStar_Pervasives_Native.None in
                                     FStar_Extraction_ML_UEnv.lookup_fv g
                                       uu____10823 in
                                   FStar_All.pipe_left FStar_Util.right
                                     uu____10806 in
                                 (match uu____10797 with
                                  | (uu____10866,fw,uu____10868,uu____10869)
                                      ->
                                      let uu____10870 =
                                        let uu____10871 =
                                          let uu____10872 =
                                            let uu____10879 =
                                              let uu____10882 =
                                                FStar_All.pipe_left
                                                  (FStar_Extraction_ML_Syntax.with_ty
                                                     FStar_Extraction_ML_Syntax.ml_string_ty)
                                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                                     (FStar_Extraction_ML_Syntax.MLC_String
                                                        "unreachable")) in
                                              [uu____10882] in
                                            (fw, uu____10879) in
                                          FStar_Extraction_ML_Syntax.MLE_App
                                            uu____10872 in
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             FStar_Extraction_ML_Syntax.ml_unit_ty)
                                          uu____10871 in
                                      (uu____10870,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        FStar_Extraction_ML_Syntax.ml_unit_ty))
                             | (uu____10885,uu____10886,(uu____10887,f_first,t_first))::rest
                                 ->
                                 let uu____10947 =
                                   FStar_List.fold_left
                                     (fun uu____10989  ->
                                        fun uu____10990  ->
                                          match (uu____10989, uu____10990)
                                          with
                                          | ((topt,f),(uu____11047,uu____11048,
                                                       (uu____11049,f_branch,t_branch)))
                                              ->
                                              let f1 =
                                                FStar_Extraction_ML_Util.join
                                                  top.FStar_Syntax_Syntax.pos
                                                  f f_branch in
                                              let topt1 =
                                                match topt with
                                                | FStar_Pervasives_Native.None
                                                     ->
                                                    FStar_Pervasives_Native.None
                                                | FStar_Pervasives_Native.Some
                                                    t1 ->
                                                    let uu____11105 =
                                                      type_leq g t1 t_branch in
                                                    if uu____11105
                                                    then
                                                      FStar_Pervasives_Native.Some
                                                        t_branch
                                                    else
                                                      (let uu____11109 =
                                                         type_leq g t_branch
                                                           t1 in
                                                       if uu____11109
                                                       then
                                                         FStar_Pervasives_Native.Some
                                                           t1
                                                       else
                                                         FStar_Pervasives_Native.None) in
                                              (topt1, f1))
                                     ((FStar_Pervasives_Native.Some t_first),
                                       f_first) rest in
                                 (match uu____10947 with
                                  | (topt,f_match) ->
                                      let mlbranches2 =
                                        FStar_All.pipe_right mlbranches1
                                          (FStar_List.map
                                             (fun uu____11204  ->
                                                match uu____11204 with
                                                | (p,(wopt,uu____11233),
                                                   (b1,uu____11235,t1)) ->
                                                    let b2 =
                                                      match topt with
                                                      | FStar_Pervasives_Native.None
                                                           ->
                                                          FStar_Extraction_ML_Syntax.apply_obj_repr
                                                            b1 t1
                                                      | FStar_Pervasives_Native.Some
                                                          uu____11254 -> b1 in
                                                    (p, wopt, b2))) in
                                      let t_match =
                                        match topt with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Extraction_ML_Syntax.MLTY_Top
                                        | FStar_Pervasives_Native.Some t1 ->
                                            t1 in
                                      let uu____11259 =
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             t_match)
                                          (FStar_Extraction_ML_Syntax.MLE_Match
                                             (e1, mlbranches2)) in
                                      (uu____11259, f_match, t_match)))))))
let ind_discriminator_body:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlmodule1
  =
  fun env  ->
    fun discName  ->
      fun constrName  ->
        let uu____11282 =
          let uu____11287 =
            FStar_TypeChecker_Env.lookup_lid
              env.FStar_Extraction_ML_UEnv.tcenv discName in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____11287 in
        match uu____11282 with
        | (uu____11312,fstar_disc_type) ->
            let wildcards =
              let uu____11321 =
                let uu____11322 = FStar_Syntax_Subst.compress fstar_disc_type in
                uu____11322.FStar_Syntax_Syntax.n in
              match uu____11321 with
              | FStar_Syntax_Syntax.Tm_arrow (binders,uu____11332) ->
                  let uu____11349 =
                    FStar_All.pipe_right binders
                      (FStar_List.filter
                         (fun uu___148_11381  ->
                            match uu___148_11381 with
                            | (uu____11388,FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____11389)) ->
                                true
                            | uu____11392 -> false)) in
                  FStar_All.pipe_right uu____11349
                    (FStar_List.map
                       (fun uu____11424  ->
                          ("_", FStar_Extraction_ML_Syntax.MLTY_Top)))
              | uu____11431 -> failwith "Discriminator must be a function" in
            let mlid = "_discr_" in
            let targ = FStar_Extraction_ML_Syntax.MLTY_Top in
            let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top in
            let discrBody =
              let uu____11442 =
                let uu____11443 =
                  let uu____11454 =
                    let uu____11455 =
                      let uu____11456 =
                        let uu____11471 =
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty targ)
                            (FStar_Extraction_ML_Syntax.MLE_Name ([], mlid)) in
                        let uu____11474 =
                          let uu____11485 =
                            let uu____11494 =
                              let uu____11495 =
                                let uu____11502 =
                                  FStar_Extraction_ML_Syntax.mlpath_of_lident
                                    constrName in
                                (uu____11502,
                                  [FStar_Extraction_ML_Syntax.MLP_Wild]) in
                              FStar_Extraction_ML_Syntax.MLP_CTor uu____11495 in
                            let uu____11505 =
                              FStar_All.pipe_left
                                (FStar_Extraction_ML_Syntax.with_ty
                                   FStar_Extraction_ML_Syntax.ml_bool_ty)
                                (FStar_Extraction_ML_Syntax.MLE_Const
                                   (FStar_Extraction_ML_Syntax.MLC_Bool true)) in
                            (uu____11494, FStar_Pervasives_Native.None,
                              uu____11505) in
                          let uu____11508 =
                            let uu____11519 =
                              let uu____11528 =
                                FStar_All.pipe_left
                                  (FStar_Extraction_ML_Syntax.with_ty
                                     FStar_Extraction_ML_Syntax.ml_bool_ty)
                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                     (FStar_Extraction_ML_Syntax.MLC_Bool
                                        false)) in
                              (FStar_Extraction_ML_Syntax.MLP_Wild,
                                FStar_Pervasives_Native.None, uu____11528) in
                            [uu____11519] in
                          uu____11485 :: uu____11508 in
                        (uu____11471, uu____11474) in
                      FStar_Extraction_ML_Syntax.MLE_Match uu____11456 in
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.ml_bool_ty) uu____11455 in
                  ((FStar_List.append wildcards [(mlid, targ)]), uu____11454) in
                FStar_Extraction_ML_Syntax.MLE_Fun uu____11443 in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty disc_ty) uu____11442 in
            let uu____11583 =
              let uu____11584 =
                let uu____11587 =
                  let uu____11588 =
                    FStar_Extraction_ML_UEnv.convIdent
                      discName.FStar_Ident.ident in
                  {
                    FStar_Extraction_ML_Syntax.mllb_name = uu____11588;
                    FStar_Extraction_ML_Syntax.mllb_tysc =
                      FStar_Pervasives_Native.None;
                    FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                    FStar_Extraction_ML_Syntax.mllb_def = discrBody;
                    FStar_Extraction_ML_Syntax.print_typ = false
                  } in
                [uu____11587] in
              (FStar_Extraction_ML_Syntax.NonRec, [], uu____11584) in
            FStar_Extraction_ML_Syntax.MLM_Let uu____11583