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
  'Auu____126 'Auu____127 .
    FStar_Extraction_ML_UEnv.env ->
      FStar_Syntax_Syntax.term ->
        ((Prims.string,'Auu____127) FStar_Pervasives_Native.tuple2 Prims.list,
          FStar_Extraction_ML_Syntax.mlty) FStar_Pervasives_Native.tuple2 ->
          FStar_Syntax_Syntax.term -> 'Auu____126
  =
  fun env  ->
    fun t  ->
      fun uu____152  ->
        fun app  ->
          match uu____152 with
          | (vars,ty) ->
              let uu____178 =
                let uu____179 = FStar_Syntax_Print.term_to_string t in
                let uu____180 =
                  let uu____181 =
                    FStar_All.pipe_right vars
                      (FStar_List.map FStar_Pervasives_Native.fst) in
                  FStar_All.pipe_right uu____181 (FStar_String.concat ", ") in
                let uu____198 =
                  FStar_Extraction_ML_Code.string_of_mlty
                    env.FStar_Extraction_ML_UEnv.currentModule ty in
                let uu____199 = FStar_Syntax_Print.term_to_string app in
                FStar_Util.format4
                  "Variable %s has a polymorphic type (forall %s. %s); expected it to be fully instantiated, but got %s"
                  uu____179 uu____180 uu____198 uu____199 in
              fail t.FStar_Syntax_Syntax.pos uu____178
let err_ill_typed_application:
  'Auu____212 'Auu____213 .
    FStar_Extraction_ML_UEnv.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term,'Auu____213) FStar_Pervasives_Native.tuple2
          Prims.list -> FStar_Extraction_ML_Syntax.mlty -> 'Auu____212
  =
  fun env  ->
    fun t  ->
      fun args  ->
        fun ty  ->
          let uu____242 =
            let uu____243 = FStar_Syntax_Print.term_to_string t in
            let uu____244 =
              let uu____245 =
                FStar_All.pipe_right args
                  (FStar_List.map
                     (fun uu____263  ->
                        match uu____263 with
                        | (x,uu____269) ->
                            FStar_Syntax_Print.term_to_string x)) in
              FStar_All.pipe_right uu____245 (FStar_String.concat " ") in
            let uu____272 =
              FStar_Extraction_ML_Code.string_of_mlty
                env.FStar_Extraction_ML_UEnv.currentModule ty in
            FStar_Util.format3
              "Ill-typed application: application is %s \n remaining args are %s\nml type of head is %s\n"
              uu____243 uu____244 uu____272 in
          fail t.FStar_Syntax_Syntax.pos uu____242
let err_value_restriction:
  'Auu____277 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> 'Auu____277
  =
  fun t  ->
    let uu____286 =
      let uu____287 = FStar_Syntax_Print.tag_of_term t in
      let uu____288 = FStar_Syntax_Print.term_to_string t in
      FStar_Util.format2
        "Refusing to generalize because of the value restriction: (%s) %s"
        uu____287 uu____288 in
    fail t.FStar_Syntax_Syntax.pos uu____286
let err_unexpected_eff:
  'Auu____297 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Extraction_ML_Syntax.e_tag ->
        FStar_Extraction_ML_Syntax.e_tag -> 'Auu____297
  =
  fun t  ->
    fun f0  ->
      fun f1  ->
        let uu____314 =
          let uu____315 = FStar_Syntax_Print.term_to_string t in
          FStar_Util.format3
            "for expression %s, Expected effect %s; got effect %s" uu____315
            (FStar_Extraction_ML_Util.eff_to_string f0)
            (FStar_Extraction_ML_Util.eff_to_string f1) in
        fail t.FStar_Syntax_Syntax.pos uu____314
let effect_as_etag:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Ident.lident -> FStar_Extraction_ML_Syntax.e_tag
  =
  let cache = FStar_Util.smap_create (Prims.parse_int "20") in
  let rec delta_norm_eff g l =
    let uu____332 = FStar_Util.smap_try_find cache l.FStar_Ident.str in
    match uu____332 with
    | FStar_Pervasives_Native.Some l1 -> l1
    | FStar_Pervasives_Native.None  ->
        let res =
          let uu____337 =
            FStar_TypeChecker_Env.lookup_effect_abbrev
              g.FStar_Extraction_ML_UEnv.tcenv [FStar_Syntax_Syntax.U_zero] l in
          match uu____337 with
          | FStar_Pervasives_Native.None  -> l
          | FStar_Pervasives_Native.Some (uu____348,c) ->
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
               let uu____381 =
                 FStar_All.pipe_right qualifiers
                   (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
               if uu____381
               then FStar_Extraction_ML_Syntax.E_PURE
               else FStar_Extraction_ML_Syntax.E_IMPURE
           | FStar_Pervasives_Native.None  ->
               FStar_Extraction_ML_Syntax.E_IMPURE)
let rec is_arity:
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t in
      let uu____400 =
        let uu____401 = FStar_Syntax_Subst.compress t1 in
        uu____401.FStar_Syntax_Syntax.n in
      match uu____400 with
      | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____404 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_ascribed uu____429 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_meta uu____456 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_uvar uu____463 -> false
      | FStar_Syntax_Syntax.Tm_constant uu____480 -> false
      | FStar_Syntax_Syntax.Tm_name uu____481 -> false
      | FStar_Syntax_Syntax.Tm_bvar uu____482 -> false
      | FStar_Syntax_Syntax.Tm_type uu____483 -> true
      | FStar_Syntax_Syntax.Tm_arrow (uu____484,c) ->
          is_arity env (FStar_Syntax_Util.comp_result c)
      | FStar_Syntax_Syntax.Tm_fvar uu____502 ->
          let t2 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Normalize.AllowUnboundUniverses;
              FStar_TypeChecker_Normalize.EraseUniverses;
              FStar_TypeChecker_Normalize.UnfoldUntil
                FStar_Syntax_Syntax.Delta_constant]
              env.FStar_Extraction_ML_UEnv.tcenv t1 in
          let uu____504 =
            let uu____505 = FStar_Syntax_Subst.compress t2 in
            uu____505.FStar_Syntax_Syntax.n in
          (match uu____504 with
           | FStar_Syntax_Syntax.Tm_fvar uu____508 -> false
           | uu____509 -> is_arity env t2)
      | FStar_Syntax_Syntax.Tm_app uu____510 ->
          let uu____525 = FStar_Syntax_Util.head_and_args t1 in
          (match uu____525 with | (head1,uu____541) -> is_arity env head1)
      | FStar_Syntax_Syntax.Tm_uinst (head1,uu____563) -> is_arity env head1
      | FStar_Syntax_Syntax.Tm_refine (x,uu____569) ->
          is_arity env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_abs (uu____574,body,uu____576) ->
          is_arity env body
      | FStar_Syntax_Syntax.Tm_let (uu____597,body) -> is_arity env body
      | FStar_Syntax_Syntax.Tm_match (uu____615,branches) ->
          (match branches with
           | (uu____653,uu____654,e)::uu____656 -> is_arity env e
           | uu____703 -> false)
let rec is_type_aux:
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Subst.compress t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____729 ->
          let uu____754 =
            let uu____755 = FStar_Syntax_Print.tag_of_term t1 in
            FStar_Util.format1 "Impossible: %s" uu____755 in
          failwith uu____754
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____756 =
            let uu____757 = FStar_Syntax_Print.tag_of_term t1 in
            FStar_Util.format1 "Impossible: %s" uu____757 in
          failwith uu____756
      | FStar_Syntax_Syntax.Tm_constant uu____758 -> false
      | FStar_Syntax_Syntax.Tm_type uu____759 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____760 -> true
      | FStar_Syntax_Syntax.Tm_arrow uu____767 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.failwith_lid ->
          false
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Extraction_ML_UEnv.is_type_name env fv
      | FStar_Syntax_Syntax.Tm_uvar (uu____782,t2) -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_bvar
          { FStar_Syntax_Syntax.ppname = uu____808;
            FStar_Syntax_Syntax.index = uu____809;
            FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_name
          { FStar_Syntax_Syntax.ppname = uu____813;
            FStar_Syntax_Syntax.index = uu____814;
            FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____819,uu____820) ->
          is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____862) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____869) ->
          let uu____890 = FStar_Syntax_Subst.open_term bs body in
          (match uu____890 with | (uu____895,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
          let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
          let uu____912 =
            let uu____917 =
              let uu____918 = FStar_Syntax_Syntax.mk_binder x in [uu____918] in
            FStar_Syntax_Subst.open_term uu____917 body in
          (match uu____912 with | (uu____919,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_let ((uu____921,lbs),body) ->
          let uu____938 = FStar_Syntax_Subst.open_let_rec lbs body in
          (match uu____938 with | (uu____945,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_match (uu____951,branches) ->
          (match branches with
           | b::uu____990 ->
               let uu____1035 = FStar_Syntax_Subst.open_branch b in
               (match uu____1035 with
                | (uu____1036,uu____1037,e) -> is_type_aux env e)
           | uu____1055 -> false)
      | FStar_Syntax_Syntax.Tm_meta (t2,uu____1073) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_app (head1,uu____1079) ->
          is_type_aux env head1
let is_type:
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      FStar_Extraction_ML_UEnv.debug env
        (fun uu____1112  ->
           let uu____1113 = FStar_Syntax_Print.tag_of_term t in
           let uu____1114 = FStar_Syntax_Print.term_to_string t in
           FStar_Util.print2 "checking is_type (%s) %s\n" uu____1113
             uu____1114);
      (let b = is_type_aux env t in
       FStar_Extraction_ML_UEnv.debug env
         (fun uu____1120  ->
            if b
            then
              let uu____1121 = FStar_Syntax_Print.term_to_string t in
              let uu____1122 = FStar_Syntax_Print.tag_of_term t in
              FStar_Util.print2 "is_type %s (%s)\n" uu____1121 uu____1122
            else
              (let uu____1124 = FStar_Syntax_Print.term_to_string t in
               let uu____1125 = FStar_Syntax_Print.tag_of_term t in
               FStar_Util.print2 "not a type %s (%s)\n" uu____1124 uu____1125));
       b)
let is_type_binder:
  'Auu____1132 .
    FStar_Extraction_ML_UEnv.env ->
      (FStar_Syntax_Syntax.bv,'Auu____1132) FStar_Pervasives_Native.tuple2 ->
        Prims.bool
  =
  fun env  ->
    fun x  ->
      is_arity env (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
let is_constructor: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1153 =
      let uu____1154 = FStar_Syntax_Subst.compress t in
      uu____1154.FStar_Syntax_Syntax.n in
    match uu____1153 with
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____1157;
          FStar_Syntax_Syntax.fv_delta = uu____1158;
          FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
            (FStar_Syntax_Syntax.Data_ctor );_}
        -> true
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____1159;
          FStar_Syntax_Syntax.fv_delta = uu____1160;
          FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
            (FStar_Syntax_Syntax.Record_ctor uu____1161);_}
        -> true
    | uu____1168 -> false
let rec is_fstar_value: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1173 =
      let uu____1174 = FStar_Syntax_Subst.compress t in
      uu____1174.FStar_Syntax_Syntax.n in
    match uu____1173 with
    | FStar_Syntax_Syntax.Tm_constant uu____1177 -> true
    | FStar_Syntax_Syntax.Tm_bvar uu____1178 -> true
    | FStar_Syntax_Syntax.Tm_fvar uu____1179 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____1180 -> true
    | FStar_Syntax_Syntax.Tm_app (head1,args) ->
        let uu____1219 = is_constructor head1 in
        if uu____1219
        then
          FStar_All.pipe_right args
            (FStar_List.for_all
               (fun uu____1235  ->
                  match uu____1235 with
                  | (te,uu____1241) -> is_fstar_value te))
        else false
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____1244) -> is_fstar_value t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____1250,uu____1251) ->
        is_fstar_value t1
    | uu____1292 -> false
let rec is_ml_value: FStar_Extraction_ML_Syntax.mlexpr -> Prims.bool =
  fun e  ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_Const uu____1297 -> true
    | FStar_Extraction_ML_Syntax.MLE_Var uu____1298 -> true
    | FStar_Extraction_ML_Syntax.MLE_Name uu____1299 -> true
    | FStar_Extraction_ML_Syntax.MLE_Fun uu____1300 -> true
    | FStar_Extraction_ML_Syntax.MLE_CTor (uu____1311,exps) ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Tuple exps ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Record (uu____1320,fields) ->
        FStar_Util.for_all
          (fun uu____1345  ->
             match uu____1345 with | (uu____1350,e1) -> is_ml_value e1)
          fields
    | uu____1352 -> false
let fresh:
  Prims.string -> (Prims.string,Prims.int) FStar_Pervasives_Native.tuple2 =
  let c = FStar_Util.mk_ref (Prims.parse_int "0") in
  fun x  ->
    FStar_Util.incr c;
    (let uu____1386 =
       let uu____1387 =
         let uu____1388 = FStar_ST.op_Bang c in
         FStar_Util.string_of_int uu____1388 in
       Prims.strcat x uu____1387 in
     let uu____1413 = FStar_ST.op_Bang c in (uu____1386, uu____1413))
let normalize_abs: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t0  ->
    let rec aux bs t copt =
      let t1 = FStar_Syntax_Subst.compress t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_abs (bs',body,copt1) ->
          aux (FStar_List.append bs bs') body copt1
      | uu____1496 ->
          let e' = FStar_Syntax_Util.unascribe t1 in
          let uu____1498 = FStar_Syntax_Util.is_fun e' in
          if uu____1498
          then aux bs e' copt
          else FStar_Syntax_Util.abs bs e' copt in
    aux [] t0 FStar_Pervasives_Native.None
let unit_binder: FStar_Syntax_Syntax.binder =
  let uu____1504 =
    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
      FStar_Syntax_Syntax.t_unit in
  FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____1504
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
      (let uu____1583 = FStar_List.hd l in
       match uu____1583 with
       | (p1,w1,e1) ->
           let uu____1617 =
             let uu____1626 = FStar_List.tl l in FStar_List.hd uu____1626 in
           (match uu____1617 with
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
                 | uu____1700 -> def)))
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
            let uu____1766 = erasable g f ty in
            if uu____1766
            then
              let uu____1767 =
                type_leq g ty FStar_Extraction_ML_Syntax.ml_unit_ty in
              (if uu____1767
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
      let uu____1778 = FStar_Extraction_ML_Util.doms_and_cod t in
      match uu____1778 with
      | (ts,r) ->
          if ts = []
          then e
          else
            (let vs = FStar_List.map (fun uu____1806  -> fresh "a") ts in
             let vs_ts = FStar_List.zip vs ts in
             let vs_es =
               let uu____1825 = FStar_List.zip vs ts in
               FStar_List.map
                 (fun uu____1843  ->
                    match uu____1843 with
                    | (v1,t1) ->
                        FStar_Extraction_ML_Syntax.with_ty t1
                          (FStar_Extraction_ML_Syntax.MLE_Var v1)) uu____1825 in
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
      let uu____1871 =
        (FStar_Options.ml_no_eta_expand_coertions ()) ||
          (let uu____1873 = FStar_Options.codegen () in
           uu____1873 = (FStar_Pervasives_Native.Some "Kremlin")) in
      if uu____1871 then e else eta_expand expect e
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
          let uu____1896 =
            type_leq_c g (FStar_Pervasives_Native.Some e) ty1 expect in
          match uu____1896 with
          | (true ,FStar_Pervasives_Native.Some e') -> e'
          | uu____1906 ->
              (FStar_Extraction_ML_UEnv.debug g
                 (fun uu____1918  ->
                    let uu____1919 =
                      FStar_Extraction_ML_Code.string_of_mlexpr
                        g.FStar_Extraction_ML_UEnv.currentModule e in
                    let uu____1920 =
                      FStar_Extraction_ML_Code.string_of_mlty
                        g.FStar_Extraction_ML_UEnv.currentModule ty1 in
                    let uu____1921 =
                      FStar_Extraction_ML_Code.string_of_mlty
                        g.FStar_Extraction_ML_UEnv.currentModule expect in
                    FStar_Util.print3
                      "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n"
                      uu____1919 uu____1920 uu____1921);
               (let uu____1922 =
                  FStar_All.pipe_left
                    (FStar_Extraction_ML_Syntax.with_ty expect)
                    (FStar_Extraction_ML_Syntax.MLE_Coerce (e, ty1, expect)) in
                maybe_eta_expand expect uu____1922))
let bv_as_mlty:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlty
  =
  fun g  ->
    fun bv  ->
      let uu____1931 = FStar_Extraction_ML_UEnv.lookup_bv g bv in
      match uu____1931 with
      | FStar_Util.Inl (uu____1932,t) -> t
      | uu____1946 -> FStar_Extraction_ML_Syntax.MLTY_Top
let rec term_as_mlty:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlty
  =
  fun g  ->
    fun t0  ->
      let rec is_top_ty t =
        match t with
        | FStar_Extraction_ML_Syntax.MLTY_Top  -> true
        | FStar_Extraction_ML_Syntax.MLTY_Named uu____1989 ->
            let uu____1996 = FStar_Extraction_ML_Util.udelta_unfold g t in
            (match uu____1996 with
             | FStar_Pervasives_Native.None  -> false
             | FStar_Pervasives_Native.Some t1 -> is_top_ty t1)
        | uu____2000 -> false in
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
      let uu____2003 = is_top_ty mlt in
      if uu____2003
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
      | FStar_Syntax_Syntax.Tm_bvar uu____2009 ->
          let uu____2010 =
            let uu____2011 = FStar_Syntax_Print.term_to_string t1 in
            FStar_Util.format1 "Impossible: Unexpected term %s" uu____2011 in
          failwith uu____2010
      | FStar_Syntax_Syntax.Tm_delayed uu____2012 ->
          let uu____2037 =
            let uu____2038 = FStar_Syntax_Print.term_to_string t1 in
            FStar_Util.format1 "Impossible: Unexpected term %s" uu____2038 in
          failwith uu____2037
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____2039 =
            let uu____2040 = FStar_Syntax_Print.term_to_string t1 in
            FStar_Util.format1 "Impossible: Unexpected term %s" uu____2040 in
          failwith uu____2039
      | FStar_Syntax_Syntax.Tm_constant uu____2041 ->
          FStar_Extraction_ML_UEnv.unknownType
      | FStar_Syntax_Syntax.Tm_uvar uu____2042 ->
          FStar_Extraction_ML_UEnv.unknownType
      | FStar_Syntax_Syntax.Tm_meta (t2,uu____2060) -> term_as_mlty' env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____2065;
             FStar_Syntax_Syntax.index = uu____2066;
             FStar_Syntax_Syntax.sort = t2;_},uu____2068)
          -> term_as_mlty' env t2
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____2076) -> term_as_mlty' env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____2082,uu____2083) ->
          term_as_mlty' env t2
      | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
      | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv []
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____2150 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____2150 with
           | (bs1,c1) ->
               let uu____2157 = binders_as_ml_binders env bs1 in
               (match uu____2157 with
                | (mlbs,env1) ->
                    let t_ret =
                      let eff =
                        FStar_TypeChecker_Env.norm_eff_name
                          env1.FStar_Extraction_ML_UEnv.tcenv
                          (FStar_Syntax_Util.comp_effect_name c1) in
                      let uu____2184 =
                        let uu____2191 =
                          FStar_TypeChecker_Env.effect_decl_opt
                            env1.FStar_Extraction_ML_UEnv.tcenv eff in
                        FStar_Util.must uu____2191 in
                      match uu____2184 with
                      | (ed,qualifiers) ->
                          let uu____2212 =
                            FStar_All.pipe_right qualifiers
                              (FStar_List.contains
                                 FStar_Syntax_Syntax.Reifiable) in
                          if uu____2212
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
                    let uu____2219 =
                      FStar_List.fold_right
                        (fun uu____2238  ->
                           fun uu____2239  ->
                             match (uu____2238, uu____2239) with
                             | ((uu____2260,t2),(tag,t')) ->
                                 (FStar_Extraction_ML_Syntax.E_PURE,
                                   (FStar_Extraction_ML_Syntax.MLTY_Fun
                                      (t2, tag, t')))) mlbs (erase1, t_ret) in
                    (match uu____2219 with | (uu____2272,t2) -> t2)))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let res =
            let uu____2297 =
              let uu____2298 = FStar_Syntax_Util.un_uinst head1 in
              uu____2298.FStar_Syntax_Syntax.n in
            match uu____2297 with
            | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
            | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv args
            | FStar_Syntax_Syntax.Tm_app (head2,args') ->
                let uu____2325 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app
                       (head2, (FStar_List.append args' args)))
                    FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos in
                term_as_mlty' env uu____2325
            | uu____2342 -> FStar_Extraction_ML_UEnv.unknownType in
          res
      | FStar_Syntax_Syntax.Tm_abs (bs,ty,uu____2345) ->
          let uu____2366 = FStar_Syntax_Subst.open_term bs ty in
          (match uu____2366 with
           | (bs1,ty1) ->
               let uu____2373 = binders_as_ml_binders env bs1 in
               (match uu____2373 with | (bts,env1) -> term_as_mlty' env1 ty1))
      | FStar_Syntax_Syntax.Tm_type uu____2398 ->
          FStar_Extraction_ML_UEnv.unknownType
      | FStar_Syntax_Syntax.Tm_let uu____2399 ->
          FStar_Extraction_ML_UEnv.unknownType
      | FStar_Syntax_Syntax.Tm_match uu____2412 ->
          FStar_Extraction_ML_UEnv.unknownType
and arg_as_mlty:
  FStar_Extraction_ML_UEnv.env ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 -> FStar_Extraction_ML_Syntax.mlty
  =
  fun g  ->
    fun uu____2436  ->
      match uu____2436 with
      | (a,uu____2442) ->
          let uu____2443 = is_type g a in
          if uu____2443
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
        let uu____2448 =
          let uu____2461 =
            FStar_TypeChecker_Env.lookup_lid g.FStar_Extraction_ML_UEnv.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____2461 with
          | ((uu____2482,fvty),uu____2484) ->
              let fvty1 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Normalize.UnfoldUntil
                     FStar_Syntax_Syntax.Delta_constant]
                  g.FStar_Extraction_ML_UEnv.tcenv fvty in
              FStar_Syntax_Util.arrow_formals fvty1 in
        match uu____2448 with
        | (formals,uu____2491) ->
            let mlargs = FStar_List.map (arg_as_mlty g) args in
            let mlargs1 =
              let n_args = FStar_List.length args in
              if (FStar_List.length formals) > n_args
              then
                let uu____2535 = FStar_Util.first_N n_args formals in
                match uu____2535 with
                | (uu____2562,rest) ->
                    let uu____2588 =
                      FStar_List.map
                        (fun uu____2596  ->
                           FStar_Extraction_ML_UEnv.erasedContent) rest in
                    FStar_List.append mlargs uu____2588
              else mlargs in
            let nm =
              let uu____2603 =
                FStar_Extraction_ML_UEnv.maybe_mangle_type_projector g fv in
              match uu____2603 with
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
      let uu____2621 =
        FStar_All.pipe_right bs
          (FStar_List.fold_left
             (fun uu____2676  ->
                fun b  ->
                  match uu____2676 with
                  | (ml_bs,env) ->
                      let uu____2732 = is_type_binder g b in
                      if uu____2732
                      then
                        let b1 = FStar_Pervasives_Native.fst b in
                        let env1 =
                          FStar_Extraction_ML_UEnv.extend_ty env b1
                            (FStar_Pervasives_Native.Some
                               FStar_Extraction_ML_Syntax.MLTY_Top) in
                        let ml_b =
                          let uu____2758 =
                            FStar_Extraction_ML_UEnv.bv_as_ml_termvar b1 in
                          (uu____2758, FStar_Extraction_ML_Syntax.ml_unit_ty) in
                        ((ml_b :: ml_bs), env1)
                      else
                        (let b1 = FStar_Pervasives_Native.fst b in
                         let t = term_as_mlty env b1.FStar_Syntax_Syntax.sort in
                         let uu____2788 =
                           FStar_Extraction_ML_UEnv.extend_bv env b1 
                             ([], t) false false false in
                         match uu____2788 with
                         | (env1,b2) ->
                             let ml_b =
                               let uu____2820 =
                                 FStar_Extraction_ML_UEnv.removeTick b2 in
                               (uu____2820, t) in
                             ((ml_b :: ml_bs), env1))) ([], g)) in
      match uu____2621 with | (ml_bs,env) -> ((FStar_List.rev ml_bs), env)
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
      | (FStar_Extraction_ML_Syntax.MLE_Seq es1,uu____2930) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (FStar_List.append es1 [e2])
      | (uu____2933,FStar_Extraction_ML_Syntax.MLE_Seq es2) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (e1 :: es2)
      | uu____2937 -> FStar_Extraction_ML_Syntax.MLE_Seq [e1; e2]
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
                    | uu____2969 when
                        (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
                          =
                          FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr
                        -> body.FStar_Extraction_ML_Syntax.expr
                    | uu____2970 ->
                        mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def
                          body)
             | uu____2971 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body))
        | uu____2974 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body)
let resugar_pat:
  FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option ->
    FStar_Extraction_ML_Syntax.mlpattern ->
      FStar_Extraction_ML_Syntax.mlpattern
  =
  fun q  ->
    fun p  ->
      match p with
      | FStar_Extraction_ML_Syntax.MLP_CTor (d,pats) ->
          let uu____2993 = FStar_Extraction_ML_Util.is_xtuple d in
          (match uu____2993 with
           | FStar_Pervasives_Native.Some n1 ->
               FStar_Extraction_ML_Syntax.MLP_Tuple pats
           | uu____2997 ->
               (match q with
                | FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Record_ctor (ty,fns)) ->
                    let path =
                      FStar_List.map FStar_Ident.text_of_id ty.FStar_Ident.ns in
                    let fs = record_fields fns pats in
                    FStar_Extraction_ML_Syntax.MLP_Record (path, fs)
                | uu____3024 -> p))
      | uu____3027 -> p
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
                     (fun uu____3086  ->
                        let uu____3087 =
                          FStar_Extraction_ML_Code.string_of_mlty
                            g.FStar_Extraction_ML_UEnv.currentModule t' in
                        let uu____3088 =
                          FStar_Extraction_ML_Code.string_of_mlty
                            g.FStar_Extraction_ML_UEnv.currentModule t in
                        FStar_Util.print2
                          "Expected pattern type %s; got pattern type %s\n"
                          uu____3087 uu____3088)
                 else ();
                 ok) in
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int
              (c,FStar_Pervasives_Native.None )) ->
              let i = FStar_Const.Const_int (c, FStar_Pervasives_Native.None) in
              let x = FStar_Extraction_ML_Syntax.gensym () in
              let when_clause =
                let uu____3128 =
                  let uu____3129 =
                    let uu____3136 =
                      let uu____3139 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.ml_int_ty)
                          (FStar_Extraction_ML_Syntax.MLE_Var x) in
                      let uu____3140 =
                        let uu____3143 =
                          let uu____3144 =
                            let uu____3145 =
                              FStar_Extraction_ML_Util.mlconst_of_const'
                                p.FStar_Syntax_Syntax.p i in
                            FStar_All.pipe_left
                              (fun _0_44  ->
                                 FStar_Extraction_ML_Syntax.MLE_Const _0_44)
                              uu____3145 in
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty
                               FStar_Extraction_ML_Syntax.ml_int_ty)
                            uu____3144 in
                        [uu____3143] in
                      uu____3139 :: uu____3140 in
                    (FStar_Extraction_ML_Util.prims_op_equality, uu____3136) in
                  FStar_Extraction_ML_Syntax.MLE_App uu____3129 in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     FStar_Extraction_ML_Syntax.ml_bool_ty) uu____3128 in
              let uu____3148 = ok FStar_Extraction_ML_Syntax.ml_int_ty in
              (g,
                (FStar_Pervasives_Native.Some
                   ((FStar_Extraction_ML_Syntax.MLP_Var x), [when_clause])),
                uu____3148)
          | FStar_Syntax_Syntax.Pat_constant s ->
              let t =
                FStar_TypeChecker_TcTerm.tc_constant FStar_Range.dummyRange s in
              let mlty = term_as_mlty g t in
              let uu____3168 =
                let uu____3177 =
                  let uu____3184 =
                    let uu____3185 =
                      FStar_Extraction_ML_Util.mlconst_of_const'
                        p.FStar_Syntax_Syntax.p s in
                    FStar_Extraction_ML_Syntax.MLP_Const uu____3185 in
                  (uu____3184, []) in
                FStar_Pervasives_Native.Some uu____3177 in
              let uu____3194 = ok mlty in (g, uu____3168, uu____3194)
          | FStar_Syntax_Syntax.Pat_var x ->
              let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort in
              let uu____3205 =
                FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false false
                  imp in
              (match uu____3205 with
               | (g1,x1) ->
                   let uu____3228 = ok mlty in
                   (g1,
                     (if imp
                      then FStar_Pervasives_Native.None
                      else
                        FStar_Pervasives_Native.Some
                          ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                     uu____3228))
          | FStar_Syntax_Syntax.Pat_wild x ->
              let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort in
              let uu____3262 =
                FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false false
                  imp in
              (match uu____3262 with
               | (g1,x1) ->
                   let uu____3285 = ok mlty in
                   (g1,
                     (if imp
                      then FStar_Pervasives_Native.None
                      else
                        FStar_Pervasives_Native.Some
                          ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                     uu____3285))
          | FStar_Syntax_Syntax.Pat_dot_term uu____3317 ->
              (g, FStar_Pervasives_Native.None, true)
          | FStar_Syntax_Syntax.Pat_cons (f,pats) ->
              let uu____3356 =
                let uu____3361 = FStar_Extraction_ML_UEnv.lookup_fv g f in
                match uu____3361 with
                | FStar_Util.Inr
                    (uu____3366,{
                                  FStar_Extraction_ML_Syntax.expr =
                                    FStar_Extraction_ML_Syntax.MLE_Name n1;
                                  FStar_Extraction_ML_Syntax.mlty =
                                    uu____3368;
                                  FStar_Extraction_ML_Syntax.loc = uu____3369;_},ttys,uu____3371)
                    -> (n1, ttys)
                | uu____3384 -> failwith "Expected a constructor" in
              (match uu____3356 with
               | (d,tys) ->
                   let nTyVars =
                     FStar_List.length (FStar_Pervasives_Native.fst tys) in
                   let uu____3406 = FStar_Util.first_N nTyVars pats in
                   (match uu____3406 with
                    | (tysVarPats,restPats) ->
                        let f_ty_opt =
                          try
                            let mlty_args =
                              FStar_All.pipe_right tysVarPats
                                (FStar_List.map
                                   (fun uu____3539  ->
                                      match uu____3539 with
                                      | (p1,uu____3547) ->
                                          (match p1.FStar_Syntax_Syntax.v
                                           with
                                           | FStar_Syntax_Syntax.Pat_dot_term
                                               (uu____3552,t) ->
                                               term_as_mlty g t
                                           | uu____3558 ->
                                               (FStar_Extraction_ML_UEnv.debug
                                                  g
                                                  (fun uu____3562  ->
                                                     let uu____3563 =
                                                       FStar_Syntax_Print.pat_to_string
                                                         p1 in
                                                     FStar_Util.print1
                                                       "Pattern %s is not extractable"
                                                       uu____3563);
                                                FStar_Exn.raise
                                                  Un_extractable)))) in
                            let f_ty =
                              FStar_Extraction_ML_Util.subst tys mlty_args in
                            let uu____3565 =
                              FStar_Extraction_ML_Util.uncurry_mlty_fun f_ty in
                            FStar_Pervasives_Native.Some uu____3565
                          with
                          | Un_extractable  -> FStar_Pervasives_Native.None in
                        let uu____3594 =
                          FStar_Util.fold_map
                            (fun g1  ->
                               fun uu____3630  ->
                                 match uu____3630 with
                                 | (p1,imp1) ->
                                     let uu____3649 =
                                       extract_one_pat true g1 p1
                                         FStar_Pervasives_Native.None in
                                     (match uu____3649 with
                                      | (g2,p2,uu____3678) -> (g2, p2))) g
                            tysVarPats in
                        (match uu____3594 with
                         | (g1,tyMLPats) ->
                             let uu____3739 =
                               FStar_Util.fold_map
                                 (fun uu____3803  ->
                                    fun uu____3804  ->
                                      match (uu____3803, uu____3804) with
                                      | ((g2,f_ty_opt1),(p1,imp1)) ->
                                          let uu____3897 =
                                            match f_ty_opt1 with
                                            | FStar_Pervasives_Native.Some
                                                (hd1::rest,res) ->
                                                ((FStar_Pervasives_Native.Some
                                                    (rest, res)),
                                                  (FStar_Pervasives_Native.Some
                                                     hd1))
                                            | uu____3957 ->
                                                (FStar_Pervasives_Native.None,
                                                  FStar_Pervasives_Native.None) in
                                          (match uu____3897 with
                                           | (f_ty_opt2,expected_ty) ->
                                               let uu____4028 =
                                                 extract_one_pat false g2 p1
                                                   expected_ty in
                                               (match uu____4028 with
                                                | (g3,p2,uu____4069) ->
                                                    ((g3, f_ty_opt2), p2))))
                                 (g1, f_ty_opt) restPats in
                             (match uu____3739 with
                              | ((g2,f_ty_opt1),restMLPats) ->
                                  let uu____4187 =
                                    let uu____4198 =
                                      FStar_All.pipe_right
                                        (FStar_List.append tyMLPats
                                           restMLPats)
                                        (FStar_List.collect
                                           (fun uu___143_4249  ->
                                              match uu___143_4249 with
                                              | FStar_Pervasives_Native.Some
                                                  x -> [x]
                                              | uu____4291 -> [])) in
                                    FStar_All.pipe_right uu____4198
                                      FStar_List.split in
                                  (match uu____4187 with
                                   | (mlPats,when_clauses) ->
                                       let pat_ty_compat =
                                         match f_ty_opt1 with
                                         | FStar_Pervasives_Native.Some
                                             ([],t) -> ok t
                                         | uu____4364 -> false in
                                       let uu____4373 =
                                         let uu____4382 =
                                           let uu____4389 =
                                             resugar_pat
                                               f.FStar_Syntax_Syntax.fv_qual
                                               (FStar_Extraction_ML_Syntax.MLP_CTor
                                                  (d, mlPats)) in
                                           let uu____4392 =
                                             FStar_All.pipe_right
                                               when_clauses
                                               FStar_List.flatten in
                                           (uu____4389, uu____4392) in
                                         FStar_Pervasives_Native.Some
                                           uu____4382 in
                                       (g2, uu____4373, pat_ty_compat))))))
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
          let uu____4483 = extract_one_pat false g1 p1 expected_t1 in
          match uu____4483 with
          | (g2,FStar_Pervasives_Native.Some (x,v1),b) -> (g2, (x, v1), b)
          | uu____4540 -> failwith "Impossible: Unable to translate pattern" in
        let mk_when_clause whens =
          match whens with
          | [] -> FStar_Pervasives_Native.None
          | hd1::tl1 ->
              let uu____4583 =
                FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd1 tl1 in
              FStar_Pervasives_Native.Some uu____4583 in
        let uu____4584 =
          extract_one_pat1 g p (FStar_Pervasives_Native.Some expected_t) in
        match uu____4584 with
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
            | FStar_Extraction_ML_Syntax.MLTY_Fun (t0,uu____4726,t1) ->
                let x = FStar_Extraction_ML_Syntax.gensym () in
                let uu____4729 =
                  let uu____4740 =
                    let uu____4749 =
                      FStar_All.pipe_left
                        (FStar_Extraction_ML_Syntax.with_ty t0)
                        (FStar_Extraction_ML_Syntax.MLE_Var x) in
                    ((x, t0), uu____4749) in
                  uu____4740 :: more_args in
                eta_args uu____4729 t1
            | FStar_Extraction_ML_Syntax.MLTY_Named (uu____4762,uu____4763)
                -> ((FStar_List.rev more_args), t)
            | uu____4786 -> failwith "Impossible: Head type is not an arrow" in
          let as_record qual1 e =
            match ((e.FStar_Extraction_ML_Syntax.expr), qual1) with
            | (FStar_Extraction_ML_Syntax.MLE_CTor
               (uu____4814,args),FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Record_ctor (tyname,fields))) ->
                let path =
                  FStar_List.map FStar_Ident.text_of_id tyname.FStar_Ident.ns in
                let fields1 = record_fields fields args in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     e.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_Record (path, fields1))
            | uu____4846 -> e in
          let resugar_and_maybe_eta qual1 e =
            let uu____4864 = eta_args [] residualType in
            match uu____4864 with
            | (eargs,tres) ->
                (match eargs with
                 | [] ->
                     let uu____4917 = as_record qual1 e in
                     FStar_Extraction_ML_Util.resugar_exp uu____4917
                 | uu____4918 ->
                     let uu____4929 = FStar_List.unzip eargs in
                     (match uu____4929 with
                      | (binders,eargs1) ->
                          (match e.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_CTor (head1,args)
                               ->
                               let body =
                                 let uu____4971 =
                                   let uu____4972 =
                                     FStar_All.pipe_left
                                       (FStar_Extraction_ML_Syntax.with_ty
                                          tres)
                                       (FStar_Extraction_ML_Syntax.MLE_CTor
                                          (head1,
                                            (FStar_List.append args eargs1))) in
                                   FStar_All.pipe_left (as_record qual1)
                                     uu____4972 in
                                 FStar_All.pipe_left
                                   FStar_Extraction_ML_Util.resugar_exp
                                   uu____4971 in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    e.FStar_Extraction_ML_Syntax.mlty)
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    (binders, body))
                           | uu____4981 ->
                               failwith "Impossible: Not a constructor"))) in
          match ((mlAppExpr.FStar_Extraction_ML_Syntax.expr), qual) with
          | (uu____4984,FStar_Pervasives_Native.None ) -> mlAppExpr
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____4988;
                FStar_Extraction_ML_Syntax.loc = uu____4989;_},mle::args),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_projector (constrname,f))) ->
              let f1 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append constrname.FStar_Ident.ns [f]) in
              let fn = FStar_Extraction_ML_Util.mlpath_of_lid f1 in
              let proj = FStar_Extraction_ML_Syntax.MLE_Proj (mle, fn) in
              let e =
                match args with
                | [] -> proj
                | uu____5016 ->
                    let uu____5019 =
                      let uu____5026 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj in
                      (uu____5026, args) in
                    FStar_Extraction_ML_Syntax.MLE_App uu____5019 in
              FStar_Extraction_ML_Syntax.with_ty
                mlAppExpr.FStar_Extraction_ML_Syntax.mlty e
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____5030;
                FStar_Extraction_ML_Syntax.loc = uu____5031;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____5039 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs)) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5039
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____5043;
                FStar_Extraction_ML_Syntax.loc = uu____5044;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____5046)) ->
              let uu____5059 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs)) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5059
          | (FStar_Extraction_ML_Syntax.MLE_Name
             mlp,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor
             )) ->
              let uu____5065 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, [])) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5065
          | (FStar_Extraction_ML_Syntax.MLE_Name
             mlp,FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____5069)) ->
              let uu____5078 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, [])) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5078
          | uu____5081 -> mlAppExpr
let maybe_downgrade_eff:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.e_tag ->
      FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.e_tag
  =
  fun g  ->
    fun f  ->
      fun t  ->
        let uu____5100 =
          (f = FStar_Extraction_ML_Syntax.E_GHOST) &&
            (type_leq g t FStar_Extraction_ML_Syntax.ml_unit_ty) in
        if uu____5100 then FStar_Extraction_ML_Syntax.E_PURE else f
let rec term_as_mlexpr:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Extraction_ML_Syntax.mlexpr,FStar_Extraction_ML_Syntax.e_tag,
        FStar_Extraction_ML_Syntax.mlty) FStar_Pervasives_Native.tuple3
  =
  fun g  ->
    fun t  ->
      let uu____5154 = term_as_mlexpr' g t in
      match uu____5154 with
      | (e,tag,ty) ->
          let tag1 = maybe_downgrade_eff g tag ty in
          (FStar_Extraction_ML_UEnv.debug g
             (fun u  ->
                let uu____5175 =
                  let uu____5176 = FStar_Syntax_Print.tag_of_term t in
                  let uu____5177 = FStar_Syntax_Print.term_to_string t in
                  let uu____5178 =
                    FStar_Extraction_ML_Code.string_of_mlty
                      g.FStar_Extraction_ML_UEnv.currentModule ty in
                  FStar_Util.format4
                    "term_as_mlexpr (%s) :  %s has ML type %s and effect %s\n"
                    uu____5176 uu____5177 uu____5178
                    (FStar_Extraction_ML_Util.eff_to_string tag1) in
                FStar_Util.print_string uu____5175);
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
          let uu____5187 = check_term_as_mlexpr' g t f ty in
          match uu____5187 with
          | (e,t1) ->
              let uu____5198 = erase g e t1 f in
              (match uu____5198 with | (r,uu____5210,t2) -> (r, t2))
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
          let uu____5220 = term_as_mlexpr g e0 in
          match uu____5220 with
          | (e,tag,t) ->
              let tag1 = maybe_downgrade_eff g tag t in
              if FStar_Extraction_ML_Util.eff_leq tag1 f
              then let uu____5239 = maybe_coerce g e t ty in (uu____5239, ty)
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
           let uu____5257 =
             let uu____5258 =
               FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos in
             let uu____5259 = FStar_Syntax_Print.tag_of_term top in
             let uu____5260 = FStar_Syntax_Print.term_to_string top in
             FStar_Util.format3 "%s: term_as_mlexpr' (%s) :  %s \n"
               uu____5258 uu____5259 uu____5260 in
           FStar_Util.print_string uu____5257);
      (let t = FStar_Syntax_Subst.compress top in
       match t.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____5268 =
             let uu____5269 = FStar_Syntax_Print.tag_of_term t in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5269 in
           failwith uu____5268
       | FStar_Syntax_Syntax.Tm_delayed uu____5276 ->
           let uu____5301 =
             let uu____5302 = FStar_Syntax_Print.tag_of_term t in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5302 in
           failwith uu____5301
       | FStar_Syntax_Syntax.Tm_uvar uu____5309 ->
           let uu____5326 =
             let uu____5327 = FStar_Syntax_Print.tag_of_term t in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5327 in
           failwith uu____5326
       | FStar_Syntax_Syntax.Tm_bvar uu____5334 ->
           let uu____5335 =
             let uu____5336 = FStar_Syntax_Print.tag_of_term t in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5336 in
           failwith uu____5335
       | FStar_Syntax_Syntax.Tm_type uu____5343 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_refine uu____5344 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_arrow uu____5351 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Mutable_alloc ))
           ->
           let uu____5369 = term_as_mlexpr' g t1 in
           (match uu____5369 with
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
            | uu____5415 -> failwith "impossible")
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_monadic (m,uu____5430)) ->
           let t2 = FStar_Syntax_Subst.compress t1 in
           (match t2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) when
                FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname ->
                let uu____5460 =
                  let uu____5467 =
                    FStar_TypeChecker_Env.effect_decl_opt
                      g.FStar_Extraction_ML_UEnv.tcenv m in
                  FStar_Util.must uu____5467 in
                (match uu____5460 with
                 | (ed,qualifiers) ->
                     let uu____5494 =
                       let uu____5495 =
                         FStar_All.pipe_right qualifiers
                           (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
                       FStar_All.pipe_right uu____5495 Prims.op_Negation in
                     if uu____5494
                     then term_as_mlexpr' g t2
                     else
                       failwith
                         "This should not happen (should have been handled at Tm_abs level)")
            | uu____5511 -> term_as_mlexpr' g t2)
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____5513) -> term_as_mlexpr' g t1
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____5519) -> term_as_mlexpr' g t1
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____5525 =
             FStar_TypeChecker_TcTerm.type_of_tot_term
               g.FStar_Extraction_ML_UEnv.tcenv t in
           (match uu____5525 with
            | (uu____5538,ty,uu____5540) ->
                let ml_ty = term_as_mlty g ty in
                let uu____5542 =
                  let uu____5543 =
                    let uu____5544 =
                      FStar_Extraction_ML_Util.mlconst_of_const'
                        t.FStar_Syntax_Syntax.pos c in
                    FStar_All.pipe_left
                      (fun _0_45  ->
                         FStar_Extraction_ML_Syntax.MLE_Const _0_45)
                      uu____5544 in
                  FStar_Extraction_ML_Syntax.with_ty ml_ty uu____5543 in
                (uu____5542, FStar_Extraction_ML_Syntax.E_PURE, ml_ty))
       | FStar_Syntax_Syntax.Tm_name uu____5545 ->
           let uu____5546 = is_type g t in
           if uu____5546
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____5554 = FStar_Extraction_ML_UEnv.lookup_term g t in
              match uu____5554 with
              | (FStar_Util.Inl uu____5567,uu____5568) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | (FStar_Util.Inr (uu____5605,x,mltys,uu____5608),qual) ->
                  (match mltys with
                   | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                       ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | ([],t1) ->
                       let uu____5654 =
                         maybe_eta_data_and_project_record g qual t1 x in
                       (uu____5654, FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | uu____5655 -> err_uninst g t mltys t))
       | FStar_Syntax_Syntax.Tm_fvar uu____5662 ->
           let uu____5663 = is_type g t in
           if uu____5663
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____5671 = FStar_Extraction_ML_UEnv.lookup_term g t in
              match uu____5671 with
              | (FStar_Util.Inl uu____5684,uu____5685) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | (FStar_Util.Inr (uu____5722,x,mltys,uu____5725),qual) ->
                  (match mltys with
                   | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                       ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | ([],t1) ->
                       let uu____5771 =
                         maybe_eta_data_and_project_record g qual t1 x in
                       (uu____5771, FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | uu____5772 -> err_uninst g t mltys t))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,copt) ->
           let uu____5802 = FStar_Syntax_Subst.open_term bs body in
           (match uu____5802 with
            | (bs1,body1) ->
                let uu____5815 = binders_as_ml_binders g bs1 in
                (match uu____5815 with
                 | (ml_bs,env) ->
                     let body2 =
                       match copt with
                       | FStar_Pervasives_Native.Some c ->
                           let uu____5848 =
                             FStar_TypeChecker_Env.is_reifiable
                               env.FStar_Extraction_ML_UEnv.tcenv c in
                           if uu____5848
                           then
                             FStar_TypeChecker_Util.reify_body
                               env.FStar_Extraction_ML_UEnv.tcenv body1
                           else body1
                       | FStar_Pervasives_Native.None  ->
                           (FStar_Extraction_ML_UEnv.debug g
                              (fun uu____5853  ->
                                 let uu____5854 =
                                   FStar_Syntax_Print.term_to_string body1 in
                                 FStar_Util.print1
                                   "No computation type for: %s\n" uu____5854);
                            body1) in
                     let uu____5855 = term_as_mlexpr env body2 in
                     (match uu____5855 with
                      | (ml_body,f,t1) ->
                          let uu____5871 =
                            FStar_List.fold_right
                              (fun uu____5890  ->
                                 fun uu____5891  ->
                                   match (uu____5890, uu____5891) with
                                   | ((uu____5912,targ),(f1,t2)) ->
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         (FStar_Extraction_ML_Syntax.MLTY_Fun
                                            (targ, f1, t2)))) ml_bs (f, t1) in
                          (match uu____5871 with
                           | (f1,tfun) ->
                               let uu____5932 =
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty tfun)
                                   (FStar_Extraction_ML_Syntax.MLE_Fun
                                      (ml_bs, ml_body)) in
                               (uu____5932, f1, tfun)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____5939);
              FStar_Syntax_Syntax.pos = uu____5940;
              FStar_Syntax_Syntax.vars = uu____5941;_},uu____5942)
           -> failwith "Unreachable? Tm_app Const_reflect"
       | FStar_Syntax_Syntax.Tm_app (head1,uu____5970::(v1,uu____5972)::[])
           when (FStar_Syntax_Util.is_fstar_tactics_embed head1) && false ->
           let uu____6013 =
             let uu____6016 = FStar_Syntax_Print.term_to_string v1 in
             FStar_Util.format2 "Trying to extract a quotation of %s"
               uu____6016 in
           let s =
             let uu____6018 =
               let uu____6019 =
                 let uu____6020 =
                   let uu____6023 = FStar_Util.marshal v1 in
                   FStar_Util.bytes_of_string uu____6023 in
                 FStar_Extraction_ML_Syntax.MLC_Bytes uu____6020 in
               FStar_Extraction_ML_Syntax.MLE_Const uu____6019 in
             FStar_Extraction_ML_Syntax.with_ty
               FStar_Extraction_ML_Syntax.ml_string_ty uu____6018 in
           let zero1 =
             FStar_Extraction_ML_Syntax.with_ty
               FStar_Extraction_ML_Syntax.ml_int_ty
               (FStar_Extraction_ML_Syntax.MLE_Const
                  (FStar_Extraction_ML_Syntax.MLC_Int
                     ("0", FStar_Pervasives_Native.None))) in
           let term_ty =
             let uu____6038 =
               FStar_Syntax_Syntax.fvar
                 FStar_Parser_Const.fstar_syntax_syntax_term
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None in
             term_as_mlty g uu____6038 in
           let marshal_from_string =
             let string_to_term_ty =
               FStar_Extraction_ML_Syntax.MLTY_Fun
                 (FStar_Extraction_ML_Syntax.ml_string_ty,
                   FStar_Extraction_ML_Syntax.E_PURE, term_ty) in
             FStar_Extraction_ML_Syntax.with_ty string_to_term_ty
               (FStar_Extraction_ML_Syntax.MLE_Name
                  (["Marshal"], "from_string")) in
           let uu____6043 =
             FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty term_ty)
               (FStar_Extraction_ML_Syntax.MLE_App
                  (marshal_from_string, [s; zero1])) in
           (uu____6043, FStar_Extraction_ML_Syntax.E_PURE, term_ty)
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let is_total rc =
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_Tot_lid)
               ||
               (FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
                  (FStar_List.existsb
                     (fun uu___144_6075  ->
                        match uu___144_6075 with
                        | FStar_Syntax_Syntax.TOTAL  -> true
                        | uu____6076 -> false))) in
           let uu____6077 =
             let uu____6082 =
               let uu____6083 = FStar_Syntax_Subst.compress head1 in
               uu____6083.FStar_Syntax_Syntax.n in
             ((head1.FStar_Syntax_Syntax.n), uu____6082) in
           (match uu____6077 with
            | (FStar_Syntax_Syntax.Tm_uvar uu____6092,uu____6093) ->
                let t1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.Iota;
                    FStar_TypeChecker_Normalize.Zeta;
                    FStar_TypeChecker_Normalize.EraseUniverses;
                    FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                    g.FStar_Extraction_ML_UEnv.tcenv t in
                term_as_mlexpr' g t1
            | (uu____6111,FStar_Syntax_Syntax.Tm_abs
               (bs,uu____6113,FStar_Pervasives_Native.Some rc)) when
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
            | (uu____6134,FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_reify )) ->
                let e =
                  let uu____6136 = FStar_List.hd args in
                  FStar_TypeChecker_Util.reify_body_with_arg
                    g.FStar_Extraction_ML_UEnv.tcenv head1 uu____6136 in
                let tm =
                  let uu____6146 =
                    let uu____6147 = FStar_TypeChecker_Util.remove_reify e in
                    let uu____6148 = FStar_List.tl args in
                    FStar_Syntax_Syntax.mk_Tm_app uu____6147 uu____6148 in
                  uu____6146 FStar_Pervasives_Native.None
                    t.FStar_Syntax_Syntax.pos in
                term_as_mlexpr' g tm
            | uu____6157 ->
                let rec extract_app is_data uu____6202 uu____6203 restArgs =
                  match (uu____6202, uu____6203) with
                  | ((mlhead,mlargs_f),(f,t1)) ->
                      (match (restArgs, t1) with
                       | ([],uu____6293) ->
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
                                | uu____6315 -> false) in
                           let uu____6316 =
                             if evaluation_order_guaranteed
                             then
                               let uu____6341 =
                                 FStar_All.pipe_right
                                   (FStar_List.rev mlargs_f)
                                   (FStar_List.map
                                      FStar_Pervasives_Native.fst) in
                               ([], uu____6341)
                             else
                               FStar_List.fold_left
                                 (fun uu____6395  ->
                                    fun uu____6396  ->
                                      match (uu____6395, uu____6396) with
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
                                             let uu____6499 =
                                               let uu____6502 =
                                                 FStar_All.pipe_left
                                                   (FStar_Extraction_ML_Syntax.with_ty
                                                      arg.FStar_Extraction_ML_Syntax.mlty)
                                                   (FStar_Extraction_ML_Syntax.MLE_Var
                                                      x) in
                                               uu____6502 :: out_args in
                                             (((x, arg) :: lbs), uu____6499)))
                                 ([], []) mlargs_f in
                           (match uu____6316 with
                            | (lbs,mlargs) ->
                                let app =
                                  let uu____6552 =
                                    FStar_All.pipe_left
                                      (FStar_Extraction_ML_Syntax.with_ty t1)
                                      (FStar_Extraction_ML_Syntax.MLE_App
                                         (mlhead, mlargs)) in
                                  FStar_All.pipe_left
                                    (maybe_eta_data_and_project_record g
                                       is_data t1) uu____6552 in
                                let l_app =
                                  FStar_List.fold_right
                                    (fun uu____6564  ->
                                       fun out  ->
                                         match uu____6564 with
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
                       | ((arg,uu____6585)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                          (formal_t,f',t2)) when
                           (is_type g arg) &&
                             (type_leq g formal_t
                                FStar_Extraction_ML_Syntax.ml_unit_ty)
                           ->
                           let uu____6616 =
                             let uu____6621 =
                               FStar_Extraction_ML_Util.join
                                 arg.FStar_Syntax_Syntax.pos f f' in
                             (uu____6621, t2) in
                           extract_app is_data
                             (mlhead,
                               ((FStar_Extraction_ML_Syntax.ml_unit,
                                  FStar_Extraction_ML_Syntax.E_PURE) ::
                               mlargs_f)) uu____6616 rest
                       | ((e0,uu____6633)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                          (tExpected,f',t2)) ->
                           let r = e0.FStar_Syntax_Syntax.pos in
                           let uu____6665 = term_as_mlexpr g e0 in
                           (match uu____6665 with
                            | (e01,f0,tInferred) ->
                                let e02 =
                                  maybe_coerce g e01 tInferred tExpected in
                                let uu____6682 =
                                  let uu____6687 =
                                    FStar_Extraction_ML_Util.join_l r
                                      [f; f'; f0] in
                                  (uu____6687, t2) in
                                extract_app is_data
                                  (mlhead, ((e02, f0) :: mlargs_f))
                                  uu____6682 rest)
                       | uu____6698 ->
                           let uu____6711 =
                             FStar_Extraction_ML_Util.udelta_unfold g t1 in
                           (match uu____6711 with
                            | FStar_Pervasives_Native.Some t2 ->
                                extract_app is_data (mlhead, mlargs_f)
                                  (f, t2) restArgs
                            | FStar_Pervasives_Native.None  ->
                                err_ill_typed_application g top restArgs t1)) in
                let extract_app_maybe_projector is_data mlhead uu____6768
                  args1 =
                  match uu____6768 with
                  | (f,t1) ->
                      (match is_data with
                       | FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_projector uu____6800)
                           ->
                           let rec remove_implicits args2 f1 t2 =
                             match (args2, t2) with
                             | ((a0,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____6878))::args3,FStar_Extraction_ML_Syntax.MLTY_Fun
                                (uu____6880,f',t3)) ->
                                 let uu____6917 =
                                   FStar_Extraction_ML_Util.join
                                     a0.FStar_Syntax_Syntax.pos f1 f' in
                                 remove_implicits args3 uu____6917 t3
                             | uu____6918 -> (args2, f1, t2) in
                           let uu____6943 = remove_implicits args1 f t1 in
                           (match uu____6943 with
                            | (args2,f1,t2) ->
                                extract_app is_data (mlhead, []) (f1, t2)
                                  args2)
                       | uu____6999 ->
                           extract_app is_data (mlhead, []) (f, t1) args1) in
                let uu____7012 = is_type g t in
                if uu____7012
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
                         (let uu____7029 =
                            let uu____7030 =
                              FStar_Extraction_ML_Syntax.string_of_mlpath
                                g.FStar_Extraction_ML_UEnv.currentModule in
                            uu____7030 = "FStar.Tactics.Builtins" in
                          Prims.op_Negation uu____7029)
                       ->
                       (match args with
                        | a::b::[] ->
                            term_as_mlexpr g (FStar_Pervasives_Native.fst a)
                        | uu____7071 ->
                            let uu____7080 =
                              FStar_Syntax_Print.args_to_string args in
                            failwith uu____7080)
                   | FStar_Syntax_Syntax.Tm_name uu____7087 ->
                       let uu____7088 =
                         let uu____7101 =
                           FStar_Extraction_ML_UEnv.lookup_term g head2 in
                         match uu____7101 with
                         | (FStar_Util.Inr (uu____7120,x1,x2,x3),q) ->
                             ((x1, x2, x3), q)
                         | uu____7165 -> failwith "FIXME Ty" in
                       (match uu____7088 with
                        | ((head_ml,(vars,t1),inst_ok),qual) ->
                            let has_typ_apps =
                              match args with
                              | (a,uu____7215)::uu____7216 -> is_type g a
                              | uu____7235 -> false in
                            let uu____7244 =
                              match vars with
                              | uu____7273::uu____7274 when
                                  (Prims.op_Negation has_typ_apps) && inst_ok
                                  -> (head_ml, t1, args)
                              | uu____7285 ->
                                  let n1 = FStar_List.length vars in
                                  if n1 <= (FStar_List.length args)
                                  then
                                    let uu____7313 =
                                      FStar_Util.first_N n1 args in
                                    (match uu____7313 with
                                     | (prefix1,rest) ->
                                         let prefixAsMLTypes =
                                           FStar_List.map
                                             (fun uu____7402  ->
                                                match uu____7402 with
                                                | (x,uu____7408) ->
                                                    term_as_mlty g x) prefix1 in
                                         let t2 =
                                           instantiate (vars, t1)
                                             prefixAsMLTypes in
                                         let head3 =
                                           match head_ml.FStar_Extraction_ML_Syntax.expr
                                           with
                                           | FStar_Extraction_ML_Syntax.MLE_Name
                                               uu____7411 ->
                                               let uu___148_7412 = head_ml in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (uu___148_7412.FStar_Extraction_ML_Syntax.expr);
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   = t2;
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___148_7412.FStar_Extraction_ML_Syntax.loc)
                                               }
                                           | FStar_Extraction_ML_Syntax.MLE_Var
                                               uu____7413 ->
                                               let uu___148_7414 = head_ml in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (uu___148_7414.FStar_Extraction_ML_Syntax.expr);
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   = t2;
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___148_7414.FStar_Extraction_ML_Syntax.loc)
                                               }
                                           | FStar_Extraction_ML_Syntax.MLE_App
                                               (head3,{
                                                        FStar_Extraction_ML_Syntax.expr
                                                          =
                                                          FStar_Extraction_ML_Syntax.MLE_Const
                                                          (FStar_Extraction_ML_Syntax.MLC_Unit
                                                          );
                                                        FStar_Extraction_ML_Syntax.mlty
                                                          = uu____7416;
                                                        FStar_Extraction_ML_Syntax.loc
                                                          = uu____7417;_}::[])
                                               ->
                                               FStar_All.pipe_right
                                                 (FStar_Extraction_ML_Syntax.MLE_App
                                                    ((let uu___149_7423 =
                                                        head3 in
                                                      {
                                                        FStar_Extraction_ML_Syntax.expr
                                                          =
                                                          (uu___149_7423.FStar_Extraction_ML_Syntax.expr);
                                                        FStar_Extraction_ML_Syntax.mlty
                                                          =
                                                          (FStar_Extraction_ML_Syntax.MLTY_Fun
                                                             (FStar_Extraction_ML_Syntax.ml_unit_ty,
                                                               FStar_Extraction_ML_Syntax.E_PURE,
                                                               t2));
                                                        FStar_Extraction_ML_Syntax.loc
                                                          =
                                                          (uu___149_7423.FStar_Extraction_ML_Syntax.loc)
                                                      }),
                                                      [FStar_Extraction_ML_Syntax.ml_unit]))
                                                 (FStar_Extraction_ML_Syntax.with_ty
                                                    t2)
                                           | uu____7424 ->
                                               failwith
                                                 "Impossible: Unexpected head term" in
                                         (head3, t2, rest))
                                  else err_uninst g head2 (vars, t1) top in
                            (match uu____7244 with
                             | (head_ml1,head_t,args1) ->
                                 (match args1 with
                                  | [] ->
                                      let uu____7485 =
                                        maybe_eta_data_and_project_record g
                                          qual head_t head_ml1 in
                                      (uu____7485,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        head_t)
                                  | uu____7486 ->
                                      extract_app_maybe_projector qual
                                        head_ml1
                                        (FStar_Extraction_ML_Syntax.E_PURE,
                                          head_t) args1)))
                   | FStar_Syntax_Syntax.Tm_fvar uu____7495 ->
                       let uu____7496 =
                         let uu____7509 =
                           FStar_Extraction_ML_UEnv.lookup_term g head2 in
                         match uu____7509 with
                         | (FStar_Util.Inr (uu____7528,x1,x2,x3),q) ->
                             ((x1, x2, x3), q)
                         | uu____7573 -> failwith "FIXME Ty" in
                       (match uu____7496 with
                        | ((head_ml,(vars,t1),inst_ok),qual) ->
                            let has_typ_apps =
                              match args with
                              | (a,uu____7623)::uu____7624 -> is_type g a
                              | uu____7643 -> false in
                            let uu____7652 =
                              match vars with
                              | uu____7681::uu____7682 when
                                  (Prims.op_Negation has_typ_apps) && inst_ok
                                  -> (head_ml, t1, args)
                              | uu____7693 ->
                                  let n1 = FStar_List.length vars in
                                  if n1 <= (FStar_List.length args)
                                  then
                                    let uu____7721 =
                                      FStar_Util.first_N n1 args in
                                    (match uu____7721 with
                                     | (prefix1,rest) ->
                                         let prefixAsMLTypes =
                                           FStar_List.map
                                             (fun uu____7810  ->
                                                match uu____7810 with
                                                | (x,uu____7816) ->
                                                    term_as_mlty g x) prefix1 in
                                         let t2 =
                                           instantiate (vars, t1)
                                             prefixAsMLTypes in
                                         let head3 =
                                           match head_ml.FStar_Extraction_ML_Syntax.expr
                                           with
                                           | FStar_Extraction_ML_Syntax.MLE_Name
                                               uu____7819 ->
                                               let uu___148_7820 = head_ml in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (uu___148_7820.FStar_Extraction_ML_Syntax.expr);
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   = t2;
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___148_7820.FStar_Extraction_ML_Syntax.loc)
                                               }
                                           | FStar_Extraction_ML_Syntax.MLE_Var
                                               uu____7821 ->
                                               let uu___148_7822 = head_ml in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (uu___148_7822.FStar_Extraction_ML_Syntax.expr);
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   = t2;
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___148_7822.FStar_Extraction_ML_Syntax.loc)
                                               }
                                           | FStar_Extraction_ML_Syntax.MLE_App
                                               (head3,{
                                                        FStar_Extraction_ML_Syntax.expr
                                                          =
                                                          FStar_Extraction_ML_Syntax.MLE_Const
                                                          (FStar_Extraction_ML_Syntax.MLC_Unit
                                                          );
                                                        FStar_Extraction_ML_Syntax.mlty
                                                          = uu____7824;
                                                        FStar_Extraction_ML_Syntax.loc
                                                          = uu____7825;_}::[])
                                               ->
                                               FStar_All.pipe_right
                                                 (FStar_Extraction_ML_Syntax.MLE_App
                                                    ((let uu___149_7831 =
                                                        head3 in
                                                      {
                                                        FStar_Extraction_ML_Syntax.expr
                                                          =
                                                          (uu___149_7831.FStar_Extraction_ML_Syntax.expr);
                                                        FStar_Extraction_ML_Syntax.mlty
                                                          =
                                                          (FStar_Extraction_ML_Syntax.MLTY_Fun
                                                             (FStar_Extraction_ML_Syntax.ml_unit_ty,
                                                               FStar_Extraction_ML_Syntax.E_PURE,
                                                               t2));
                                                        FStar_Extraction_ML_Syntax.loc
                                                          =
                                                          (uu___149_7831.FStar_Extraction_ML_Syntax.loc)
                                                      }),
                                                      [FStar_Extraction_ML_Syntax.ml_unit]))
                                                 (FStar_Extraction_ML_Syntax.with_ty
                                                    t2)
                                           | uu____7832 ->
                                               failwith
                                                 "Impossible: Unexpected head term" in
                                         (head3, t2, rest))
                                  else err_uninst g head2 (vars, t1) top in
                            (match uu____7652 with
                             | (head_ml1,head_t,args1) ->
                                 (match args1 with
                                  | [] ->
                                      let uu____7893 =
                                        maybe_eta_data_and_project_record g
                                          qual head_t head_ml1 in
                                      (uu____7893,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        head_t)
                                  | uu____7894 ->
                                      extract_app_maybe_projector qual
                                        head_ml1
                                        (FStar_Extraction_ML_Syntax.E_PURE,
                                          head_t) args1)))
                   | uu____7903 ->
                       let uu____7904 = term_as_mlexpr g head2 in
                       (match uu____7904 with
                        | (head3,f,t1) ->
                            extract_app_maybe_projector
                              FStar_Pervasives_Native.None head3 (f, t1) args)))
       | FStar_Syntax_Syntax.Tm_ascribed (e0,(tc,uu____7922),f) ->
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
           let uu____7989 = check_term_as_mlexpr g e0 f1 t1 in
           (match uu____7989 with | (e,t2) -> (e, f1, t2))
       | FStar_Syntax_Syntax.Tm_let ((is_rec,lbs),e') ->
           let top_level = FStar_Syntax_Syntax.is_top_level lbs in
           let uu____8020 =
             if is_rec
             then FStar_Syntax_Subst.open_let_rec lbs e'
             else
               (let uu____8034 = FStar_Syntax_Syntax.is_top_level lbs in
                if uu____8034
                then (lbs, e')
                else
                  (let lb = FStar_List.hd lbs in
                   let x =
                     let uu____8048 =
                       FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                     FStar_Syntax_Syntax.freshen_bv uu____8048 in
                   let lb1 =
                     let uu___150_8050 = lb in
                     {
                       FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                       FStar_Syntax_Syntax.lbunivs =
                         (uu___150_8050.FStar_Syntax_Syntax.lbunivs);
                       FStar_Syntax_Syntax.lbtyp =
                         (uu___150_8050.FStar_Syntax_Syntax.lbtyp);
                       FStar_Syntax_Syntax.lbeff =
                         (uu___150_8050.FStar_Syntax_Syntax.lbeff);
                       FStar_Syntax_Syntax.lbdef =
                         (uu___150_8050.FStar_Syntax_Syntax.lbdef)
                     } in
                   let e'1 =
                     FStar_Syntax_Subst.subst
                       [FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x)] e' in
                   ([lb1], e'1))) in
           (match uu____8020 with
            | (lbs1,e'1) ->
                let lbs2 =
                  if top_level
                  then
                    FStar_All.pipe_right lbs1
                      (FStar_List.map
                         (fun lb  ->
                            let tcenv =
                              let uu____8082 =
                                FStar_Ident.lid_of_path
                                  (FStar_List.append
                                     (FStar_Pervasives_Native.fst
                                        g.FStar_Extraction_ML_UEnv.currentModule)
                                     [FStar_Pervasives_Native.snd
                                        g.FStar_Extraction_ML_UEnv.currentModule])
                                  FStar_Range.dummyRange in
                              FStar_TypeChecker_Env.set_current_module
                                g.FStar_Extraction_ML_UEnv.tcenv uu____8082 in
                            FStar_Extraction_ML_UEnv.debug g
                              (fun uu____8089  ->
                                 FStar_Options.set_option "debug_level"
                                   (FStar_Options.List
                                      [FStar_Options.String "Norm";
                                      FStar_Options.String "Extraction"]));
                            (let lbdef =
                               let uu____8093 = FStar_Options.ml_ish () in
                               if uu____8093
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
                             let uu___151_8097 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___151_8097.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___151_8097.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___151_8097.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___151_8097.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef
                             })))
                  else lbs1 in
                let maybe_generalize uu____8120 =
                  match uu____8120 with
                  | { FStar_Syntax_Syntax.lbname = lbname_;
                      FStar_Syntax_Syntax.lbunivs = uu____8140;
                      FStar_Syntax_Syntax.lbtyp = t1;
                      FStar_Syntax_Syntax.lbeff = lbeff;
                      FStar_Syntax_Syntax.lbdef = e;_} ->
                      let f_e = effect_as_etag g lbeff in
                      let t2 = FStar_Syntax_Subst.compress t1 in
                      (match t2.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                           let uu____8210 = FStar_List.hd bs in
                           FStar_All.pipe_right uu____8210 (is_type_binder g)
                           ->
                           let uu____8223 = FStar_Syntax_Subst.open_comp bs c in
                           (match uu____8223 with
                            | (bs1,c1) ->
                                let uu____8248 =
                                  let uu____8255 =
                                    FStar_Util.prefix_until
                                      (fun x  ->
                                         let uu____8291 = is_type_binder g x in
                                         Prims.op_Negation uu____8291) bs1 in
                                  match uu____8255 with
                                  | FStar_Pervasives_Native.None  ->
                                      (bs1,
                                        (FStar_Syntax_Util.comp_result c1))
                                  | FStar_Pervasives_Native.Some (bs2,b,rest)
                                      ->
                                      let uu____8379 =
                                        FStar_Syntax_Util.arrow (b :: rest)
                                          c1 in
                                      (bs2, uu____8379) in
                                (match uu____8248 with
                                 | (tbinders,tbody) ->
                                     let n_tbinders =
                                       FStar_List.length tbinders in
                                     let e1 =
                                       let uu____8424 = normalize_abs e in
                                       FStar_All.pipe_right uu____8424
                                         FStar_Syntax_Util.unmeta in
                                     (match e1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Tm_abs
                                          (bs2,body,copt) ->
                                          let uu____8466 =
                                            FStar_Syntax_Subst.open_term bs2
                                              body in
                                          (match uu____8466 with
                                           | (bs3,body1) ->
                                               if
                                                 n_tbinders <=
                                                   (FStar_List.length bs3)
                                               then
                                                 let uu____8519 =
                                                   FStar_Util.first_N
                                                     n_tbinders bs3 in
                                                 (match uu____8519 with
                                                  | (targs,rest_args) ->
                                                      let expected_source_ty
                                                        =
                                                        let s =
                                                          FStar_List.map2
                                                            (fun uu____8607 
                                                               ->
                                                               fun uu____8608
                                                                  ->
                                                                 match 
                                                                   (uu____8607,
                                                                    uu____8608)
                                                                 with
                                                                 | ((x,uu____8626),
                                                                    (y,uu____8628))
                                                                    ->
                                                                    let uu____8637
                                                                    =
                                                                    let uu____8644
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    y in
                                                                    (x,
                                                                    uu____8644) in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____8637)
                                                            tbinders targs in
                                                        FStar_Syntax_Subst.subst
                                                          s tbody in
                                                      let env =
                                                        FStar_List.fold_left
                                                          (fun env  ->
                                                             fun uu____8655 
                                                               ->
                                                               match uu____8655
                                                               with
                                                               | (a,uu____8661)
                                                                   ->
                                                                   FStar_Extraction_ML_UEnv.extend_ty
                                                                    env a
                                                                    FStar_Pervasives_Native.None)
                                                          g targs in
                                                      let expected_t =
                                                        term_as_mlty env
                                                          expected_source_ty in
                                                      let polytype =
                                                        let uu____8674 =
                                                          FStar_All.pipe_right
                                                            targs
                                                            (FStar_List.map
                                                               (fun
                                                                  uu____8704 
                                                                  ->
                                                                  match uu____8704
                                                                  with
                                                                  | (x,uu____8714)
                                                                    ->
                                                                    FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                                    x)) in
                                                        (uu____8674,
                                                          expected_t) in
                                                      let add_unit =
                                                        match rest_args with
                                                        | [] ->
                                                            let uu____8726 =
                                                              is_fstar_value
                                                                body1 in
                                                            Prims.op_Negation
                                                              uu____8726
                                                        | uu____8727 -> false in
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
                                          uu____8796 ->
                                          let env =
                                            FStar_List.fold_left
                                              (fun env  ->
                                                 fun uu____8813  ->
                                                   match uu____8813 with
                                                   | (a,uu____8819) ->
                                                       FStar_Extraction_ML_UEnv.extend_ty
                                                         env a
                                                         FStar_Pervasives_Native.None)
                                              g tbinders in
                                          let expected_t =
                                            term_as_mlty env tbody in
                                          let polytype =
                                            let uu____8832 =
                                              FStar_All.pipe_right tbinders
                                                (FStar_List.map
                                                   (fun uu____8856  ->
                                                      match uu____8856 with
                                                      | (x,uu____8866) ->
                                                          FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                            x)) in
                                            (uu____8832, expected_t) in
                                          let args =
                                            FStar_All.pipe_right tbinders
                                              (FStar_List.map
                                                 (fun uu____8886  ->
                                                    match uu____8886 with
                                                    | (bv,uu____8892) ->
                                                        let uu____8893 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            bv in
                                                        FStar_All.pipe_right
                                                          uu____8893
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
                                          uu____8947 ->
                                          let env =
                                            FStar_List.fold_left
                                              (fun env  ->
                                                 fun uu____8958  ->
                                                   match uu____8958 with
                                                   | (a,uu____8964) ->
                                                       FStar_Extraction_ML_UEnv.extend_ty
                                                         env a
                                                         FStar_Pervasives_Native.None)
                                              g tbinders in
                                          let expected_t =
                                            term_as_mlty env tbody in
                                          let polytype =
                                            let uu____8977 =
                                              FStar_All.pipe_right tbinders
                                                (FStar_List.map
                                                   (fun uu____9001  ->
                                                      match uu____9001 with
                                                      | (x,uu____9011) ->
                                                          FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                            x)) in
                                            (uu____8977, expected_t) in
                                          let args =
                                            FStar_All.pipe_right tbinders
                                              (FStar_List.map
                                                 (fun uu____9031  ->
                                                    match uu____9031 with
                                                    | (bv,uu____9037) ->
                                                        let uu____9038 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            bv in
                                                        FStar_All.pipe_right
                                                          uu____9038
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
                                          uu____9092 ->
                                          let env =
                                            FStar_List.fold_left
                                              (fun env  ->
                                                 fun uu____9103  ->
                                                   match uu____9103 with
                                                   | (a,uu____9109) ->
                                                       FStar_Extraction_ML_UEnv.extend_ty
                                                         env a
                                                         FStar_Pervasives_Native.None)
                                              g tbinders in
                                          let expected_t =
                                            term_as_mlty env tbody in
                                          let polytype =
                                            let uu____9122 =
                                              FStar_All.pipe_right tbinders
                                                (FStar_List.map
                                                   (fun uu____9146  ->
                                                      match uu____9146 with
                                                      | (x,uu____9156) ->
                                                          FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                            x)) in
                                            (uu____9122, expected_t) in
                                          let args =
                                            FStar_All.pipe_right tbinders
                                              (FStar_List.map
                                                 (fun uu____9176  ->
                                                    match uu____9176 with
                                                    | (bv,uu____9182) ->
                                                        let uu____9183 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            bv in
                                                        FStar_All.pipe_right
                                                          uu____9183
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
                                      | uu____9237 ->
                                          err_value_restriction e1)))
                       | uu____9256 ->
                           let expected_t = term_as_mlty g t2 in
                           (lbname_, f_e, (t2, ([], ([], expected_t))),
                             false, e)) in
                let check_lb env uu____9360 =
                  match uu____9360 with
                  | (nm,(lbname,f,(t1,(targs,polytype)),add_unit,e)) ->
                      let env1 =
                        FStar_List.fold_left
                          (fun env1  ->
                             fun uu____9495  ->
                               match uu____9495 with
                               | (a,uu____9501) ->
                                   FStar_Extraction_ML_UEnv.extend_ty env1 a
                                     FStar_Pervasives_Native.None) env targs in
                      let expected_t = FStar_Pervasives_Native.snd polytype in
                      let uu____9503 =
                        check_term_as_mlexpr env1 e f expected_t in
                      (match uu____9503 with
                       | (e1,uu____9513) ->
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
                let uu____9580 =
                  FStar_List.fold_right
                    (fun lb  ->
                       fun uu____9671  ->
                         match uu____9671 with
                         | (env,lbs4) ->
                             let uu____9796 = lb in
                             (match uu____9796 with
                              | (lbname,uu____9844,(t1,(uu____9846,polytype)),add_unit,uu____9849)
                                  ->
                                  let uu____9862 =
                                    FStar_Extraction_ML_UEnv.extend_lb env
                                      lbname t1 polytype add_unit true in
                                  (match uu____9862 with
                                   | (env1,nm) -> (env1, ((nm, lb) :: lbs4)))))
                    lbs3 (g, []) in
                (match uu____9580 with
                 | (env_body,lbs4) ->
                     let env_def = if is_rec then env_body else g in
                     let lbs5 =
                       FStar_All.pipe_right lbs4
                         (FStar_List.map (check_lb env_def)) in
                     let e'_rng = e'1.FStar_Syntax_Syntax.pos in
                     let uu____10139 = term_as_mlexpr env_body e'1 in
                     (match uu____10139 with
                      | (e'2,f',t') ->
                          let f =
                            let uu____10156 =
                              let uu____10159 =
                                FStar_List.map FStar_Pervasives_Native.fst
                                  lbs5 in
                              f' :: uu____10159 in
                            FStar_Extraction_ML_Util.join_l e'_rng
                              uu____10156 in
                          let is_rec1 =
                            if is_rec = true
                            then FStar_Extraction_ML_Syntax.Rec
                            else FStar_Extraction_ML_Syntax.NonRec in
                          let uu____10168 =
                            let uu____10169 =
                              let uu____10170 =
                                let uu____10171 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    lbs5 in
                                (is_rec1, [], uu____10171) in
                              mk_MLE_Let top_level uu____10170 e'2 in
                            let uu____10182 =
                              FStar_Extraction_ML_Util.mlloc_of_range
                                t.FStar_Syntax_Syntax.pos in
                            FStar_Extraction_ML_Syntax.with_ty_loc t'
                              uu____10169 uu____10182 in
                          (uu____10168, f, t'))))
       | FStar_Syntax_Syntax.Tm_match (scrutinee,pats) ->
           let uu____10221 = term_as_mlexpr g scrutinee in
           (match uu____10221 with
            | (e,f_e,t_e) ->
                let uu____10237 = check_pats_for_ite pats in
                (match uu____10237 with
                 | (b,then_e,else_e) ->
                     let no_lift x t1 = x in
                     if b
                     then
                       (match (then_e, else_e) with
                        | (FStar_Pervasives_Native.Some
                           then_e1,FStar_Pervasives_Native.Some else_e1) ->
                            let uu____10294 = term_as_mlexpr g then_e1 in
                            (match uu____10294 with
                             | (then_mle,f_then,t_then) ->
                                 let uu____10310 = term_as_mlexpr g else_e1 in
                                 (match uu____10310 with
                                  | (else_mle,f_else,t_else) ->
                                      let uu____10326 =
                                        let uu____10335 =
                                          type_leq g t_then t_else in
                                        if uu____10335
                                        then (t_else, no_lift)
                                        else
                                          (let uu____10349 =
                                             type_leq g t_else t_then in
                                           if uu____10349
                                           then (t_then, no_lift)
                                           else
                                             (FStar_Extraction_ML_Syntax.MLTY_Top,
                                               FStar_Extraction_ML_Syntax.apply_obj_repr)) in
                                      (match uu____10326 with
                                       | (t_branch,maybe_lift1) ->
                                           let uu____10383 =
                                             let uu____10384 =
                                               let uu____10385 =
                                                 let uu____10394 =
                                                   maybe_lift1 then_mle
                                                     t_then in
                                                 let uu____10395 =
                                                   let uu____10398 =
                                                     maybe_lift1 else_mle
                                                       t_else in
                                                   FStar_Pervasives_Native.Some
                                                     uu____10398 in
                                                 (e, uu____10394,
                                                   uu____10395) in
                                               FStar_Extraction_ML_Syntax.MLE_If
                                                 uu____10385 in
                                             FStar_All.pipe_left
                                               (FStar_Extraction_ML_Syntax.with_ty
                                                  t_branch) uu____10384 in
                                           let uu____10401 =
                                             FStar_Extraction_ML_Util.join
                                               then_e1.FStar_Syntax_Syntax.pos
                                               f_then f_else in
                                           (uu____10383, uu____10401,
                                             t_branch))))
                        | uu____10402 ->
                            failwith
                              "ITE pats matched but then and else expressions not found?")
                     else
                       (let uu____10418 =
                          FStar_All.pipe_right pats
                            (FStar_Util.fold_map
                               (fun compat  ->
                                  fun br  ->
                                    let uu____10527 =
                                      FStar_Syntax_Subst.open_branch br in
                                    match uu____10527 with
                                    | (pat,when_opt,branch1) ->
                                        let uu____10571 =
                                          extract_pat g pat t_e in
                                        (match uu____10571 with
                                         | (env,p,pat_t_compat) ->
                                             let uu____10629 =
                                               match when_opt with
                                               | FStar_Pervasives_Native.None
                                                    ->
                                                   (FStar_Pervasives_Native.None,
                                                     FStar_Extraction_ML_Syntax.E_PURE)
                                               | FStar_Pervasives_Native.Some
                                                   w ->
                                                   let uu____10651 =
                                                     term_as_mlexpr env w in
                                                   (match uu____10651 with
                                                    | (w1,f_w,t_w) ->
                                                        let w2 =
                                                          maybe_coerce env w1
                                                            t_w
                                                            FStar_Extraction_ML_Syntax.ml_bool_ty in
                                                        ((FStar_Pervasives_Native.Some
                                                            w2), f_w)) in
                                             (match uu____10629 with
                                              | (when_opt1,f_when) ->
                                                  let uu____10700 =
                                                    term_as_mlexpr env
                                                      branch1 in
                                                  (match uu____10700 with
                                                   | (mlbranch,f_branch,t_branch)
                                                       ->
                                                       let uu____10734 =
                                                         FStar_All.pipe_right
                                                           p
                                                           (FStar_List.map
                                                              (fun
                                                                 uu____10811 
                                                                 ->
                                                                 match uu____10811
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
                                                         uu____10734)))))
                               true) in
                        match uu____10418 with
                        | (pat_t_compat,mlbranches) ->
                            let mlbranches1 = FStar_List.flatten mlbranches in
                            let e1 =
                              if pat_t_compat
                              then e
                              else
                                (FStar_Extraction_ML_UEnv.debug g
                                   (fun uu____10976  ->
                                      let uu____10977 =
                                        FStar_Extraction_ML_Code.string_of_mlexpr
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          e in
                                      let uu____10978 =
                                        FStar_Extraction_ML_Code.string_of_mlty
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          t_e in
                                      FStar_Util.print2
                                        "Coercing scrutinee %s from type %s because pattern type is incompatible\n"
                                        uu____10977 uu____10978);
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty t_e)
                                   (FStar_Extraction_ML_Syntax.MLE_Coerce
                                      (e, t_e,
                                        FStar_Extraction_ML_Syntax.MLTY_Top))) in
                            (match mlbranches1 with
                             | [] ->
                                 let uu____11003 =
                                   let uu____11012 =
                                     let uu____11029 =
                                       FStar_Syntax_Syntax.lid_as_fv
                                         FStar_Parser_Const.failwith_lid
                                         FStar_Syntax_Syntax.Delta_constant
                                         FStar_Pervasives_Native.None in
                                     FStar_Extraction_ML_UEnv.lookup_fv g
                                       uu____11029 in
                                   FStar_All.pipe_left FStar_Util.right
                                     uu____11012 in
                                 (match uu____11003 with
                                  | (uu____11072,fw,uu____11074,uu____11075)
                                      ->
                                      let uu____11076 =
                                        let uu____11077 =
                                          let uu____11078 =
                                            let uu____11085 =
                                              let uu____11088 =
                                                FStar_All.pipe_left
                                                  (FStar_Extraction_ML_Syntax.with_ty
                                                     FStar_Extraction_ML_Syntax.ml_string_ty)
                                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                                     (FStar_Extraction_ML_Syntax.MLC_String
                                                        "unreachable")) in
                                              [uu____11088] in
                                            (fw, uu____11085) in
                                          FStar_Extraction_ML_Syntax.MLE_App
                                            uu____11078 in
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             FStar_Extraction_ML_Syntax.ml_unit_ty)
                                          uu____11077 in
                                      (uu____11076,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        FStar_Extraction_ML_Syntax.ml_unit_ty))
                             | (uu____11091,uu____11092,(uu____11093,f_first,t_first))::rest
                                 ->
                                 let uu____11153 =
                                   FStar_List.fold_left
                                     (fun uu____11195  ->
                                        fun uu____11196  ->
                                          match (uu____11195, uu____11196)
                                          with
                                          | ((topt,f),(uu____11253,uu____11254,
                                                       (uu____11255,f_branch,t_branch)))
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
                                                    let uu____11311 =
                                                      type_leq g t1 t_branch in
                                                    if uu____11311
                                                    then
                                                      FStar_Pervasives_Native.Some
                                                        t_branch
                                                    else
                                                      (let uu____11315 =
                                                         type_leq g t_branch
                                                           t1 in
                                                       if uu____11315
                                                       then
                                                         FStar_Pervasives_Native.Some
                                                           t1
                                                       else
                                                         FStar_Pervasives_Native.None) in
                                              (topt1, f1))
                                     ((FStar_Pervasives_Native.Some t_first),
                                       f_first) rest in
                                 (match uu____11153 with
                                  | (topt,f_match) ->
                                      let mlbranches2 =
                                        FStar_All.pipe_right mlbranches1
                                          (FStar_List.map
                                             (fun uu____11410  ->
                                                match uu____11410 with
                                                | (p,(wopt,uu____11439),
                                                   (b1,uu____11441,t1)) ->
                                                    let b2 =
                                                      match topt with
                                                      | FStar_Pervasives_Native.None
                                                           ->
                                                          FStar_Extraction_ML_Syntax.apply_obj_repr
                                                            b1 t1
                                                      | FStar_Pervasives_Native.Some
                                                          uu____11460 -> b1 in
                                                    (p, wopt, b2))) in
                                      let t_match =
                                        match topt with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Extraction_ML_Syntax.MLTY_Top
                                        | FStar_Pervasives_Native.Some t1 ->
                                            t1 in
                                      let uu____11465 =
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             t_match)
                                          (FStar_Extraction_ML_Syntax.MLE_Match
                                             (e1, mlbranches2)) in
                                      (uu____11465, f_match, t_match)))))))
let ind_discriminator_body:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlmodule1
  =
  fun env  ->
    fun discName  ->
      fun constrName  ->
        let uu____11488 =
          let uu____11493 =
            FStar_TypeChecker_Env.lookup_lid
              env.FStar_Extraction_ML_UEnv.tcenv discName in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____11493 in
        match uu____11488 with
        | (uu____11518,fstar_disc_type) ->
            let wildcards =
              let uu____11531 =
                let uu____11532 = FStar_Syntax_Subst.compress fstar_disc_type in
                uu____11532.FStar_Syntax_Syntax.n in
              match uu____11531 with
              | FStar_Syntax_Syntax.Tm_arrow (binders,uu____11546) ->
                  let uu____11563 =
                    FStar_All.pipe_right binders
                      (FStar_List.filter
                         (fun uu___145_11595  ->
                            match uu___145_11595 with
                            | (uu____11602,FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____11603)) ->
                                true
                            | uu____11606 -> false)) in
                  FStar_All.pipe_right uu____11563
                    (FStar_List.map
                       (fun uu____11647  ->
                          let uu____11654 = fresh "_" in
                          (uu____11654, FStar_Extraction_ML_Syntax.MLTY_Top)))
              | uu____11663 -> failwith "Discriminator must be a function" in
            let mlid = fresh "_discr_" in
            let targ = FStar_Extraction_ML_Syntax.MLTY_Top in
            let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top in
            let discrBody =
              let uu____11682 =
                let uu____11683 =
                  let uu____11694 =
                    let uu____11695 =
                      let uu____11696 =
                        let uu____11711 =
                          let uu____11712 =
                            let uu____11713 =
                              let uu____11714 =
                                FStar_Extraction_ML_Syntax.idsym mlid in
                              ([], uu____11714) in
                            FStar_Extraction_ML_Syntax.MLE_Name uu____11713 in
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty targ)
                            uu____11712 in
                        let uu____11717 =
                          let uu____11728 =
                            let uu____11737 =
                              let uu____11738 =
                                let uu____11745 =
                                  FStar_Extraction_ML_Syntax.mlpath_of_lident
                                    constrName in
                                (uu____11745,
                                  [FStar_Extraction_ML_Syntax.MLP_Wild]) in
                              FStar_Extraction_ML_Syntax.MLP_CTor uu____11738 in
                            let uu____11748 =
                              FStar_All.pipe_left
                                (FStar_Extraction_ML_Syntax.with_ty
                                   FStar_Extraction_ML_Syntax.ml_bool_ty)
                                (FStar_Extraction_ML_Syntax.MLE_Const
                                   (FStar_Extraction_ML_Syntax.MLC_Bool true)) in
                            (uu____11737, FStar_Pervasives_Native.None,
                              uu____11748) in
                          let uu____11751 =
                            let uu____11762 =
                              let uu____11771 =
                                FStar_All.pipe_left
                                  (FStar_Extraction_ML_Syntax.with_ty
                                     FStar_Extraction_ML_Syntax.ml_bool_ty)
                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                     (FStar_Extraction_ML_Syntax.MLC_Bool
                                        false)) in
                              (FStar_Extraction_ML_Syntax.MLP_Wild,
                                FStar_Pervasives_Native.None, uu____11771) in
                            [uu____11762] in
                          uu____11728 :: uu____11751 in
                        (uu____11711, uu____11717) in
                      FStar_Extraction_ML_Syntax.MLE_Match uu____11696 in
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.ml_bool_ty) uu____11695 in
                  ((FStar_List.append wildcards [(mlid, targ)]), uu____11694) in
                FStar_Extraction_ML_Syntax.MLE_Fun uu____11683 in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty disc_ty) uu____11682 in
            let uu____11846 =
              let uu____11847 =
                let uu____11850 =
                  let uu____11851 =
                    FStar_Extraction_ML_UEnv.convIdent
                      discName.FStar_Ident.ident in
                  {
                    FStar_Extraction_ML_Syntax.mllb_name = uu____11851;
                    FStar_Extraction_ML_Syntax.mllb_tysc =
                      FStar_Pervasives_Native.None;
                    FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                    FStar_Extraction_ML_Syntax.mllb_def = discrBody;
                    FStar_Extraction_ML_Syntax.print_typ = false
                  } in
                [uu____11850] in
              (FStar_Extraction_ML_Syntax.NonRec, [], uu____11847) in
            FStar_Extraction_ML_Syntax.MLM_Let uu____11846