open Prims
exception Un_extractable 
let uu___is_Un_extractable : Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Un_extractable  -> true | uu____5 -> false
  
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
  
let record_fields :
  'Auu____65 .
    FStar_Ident.ident Prims.list ->
      'Auu____65 Prims.list ->
        (Prims.string,'Auu____65) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun fs  ->
    fun vs  ->
      FStar_List.map2 (fun f  -> fun e  -> ((f.FStar_Ident.idText), e)) fs vs
  
let fail : 'Auu____102 . FStar_Range.range -> Prims.string -> 'Auu____102 =
  fun r  ->
    fun msg  ->
      (let uu____112 =
         let uu____113 = FStar_Range.string_of_range r  in
         FStar_Util.format2 "%s: %s\n" uu____113 msg  in
       FStar_All.pipe_left FStar_Util.print_string uu____112);
      failwith msg
  
let err_uninst :
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
                let uu____179 = FStar_Syntax_Print.term_to_string t  in
                let uu____180 =
                  let uu____181 =
                    FStar_All.pipe_right vars
                      (FStar_List.map FStar_Pervasives_Native.fst)
                     in
                  FStar_All.pipe_right uu____181 (FStar_String.concat ", ")
                   in
                let uu____198 =
                  FStar_Extraction_ML_Code.string_of_mlty
                    env.FStar_Extraction_ML_UEnv.currentModule ty
                   in
                let uu____199 = FStar_Syntax_Print.term_to_string app  in
                FStar_Util.format4
                  "Variable %s has a polymorphic type (forall %s. %s); expected it to be fully instantiated, but got %s"
                  uu____179 uu____180 uu____198 uu____199
                 in
              fail t.FStar_Syntax_Syntax.pos uu____178
  
let err_ill_typed_application :
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
            let uu____243 = FStar_Syntax_Print.term_to_string t  in
            let uu____244 =
              let uu____245 =
                FStar_All.pipe_right args
                  (FStar_List.map
                     (fun uu____263  ->
                        match uu____263 with
                        | (x,uu____269) ->
                            FStar_Syntax_Print.term_to_string x))
                 in
              FStar_All.pipe_right uu____245 (FStar_String.concat " ")  in
            let uu____272 =
              FStar_Extraction_ML_Code.string_of_mlty
                env.FStar_Extraction_ML_UEnv.currentModule ty
               in
            FStar_Util.format3
              "Ill-typed application: application is %s \n remaining args are %s\nml type of head is %s\n"
              uu____243 uu____244 uu____272
             in
          fail t.FStar_Syntax_Syntax.pos uu____242
  
let err_value_restriction :
  'Auu____277 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> 'Auu____277
  =
  fun t  ->
    let uu____286 =
      let uu____287 = FStar_Syntax_Print.tag_of_term t  in
      let uu____288 = FStar_Syntax_Print.term_to_string t  in
      FStar_Util.format2
        "Refusing to generalize because of the value restriction: (%s) %s"
        uu____287 uu____288
       in
    fail t.FStar_Syntax_Syntax.pos uu____286
  
let err_unexpected_eff :
  'Auu____297 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Extraction_ML_Syntax.e_tag ->
        FStar_Extraction_ML_Syntax.e_tag -> 'Auu____297
  =
  fun t  ->
    fun f0  ->
      fun f1  ->
        let uu____314 =
          let uu____315 = FStar_Syntax_Print.term_to_string t  in
          FStar_Util.format3
            "for expression %s, Expected effect %s; got effect %s" uu____315
            (FStar_Extraction_ML_Util.eff_to_string f0)
            (FStar_Extraction_ML_Util.eff_to_string f1)
           in
        fail t.FStar_Syntax_Syntax.pos uu____314
  
let effect_as_etag :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Ident.lident -> FStar_Extraction_ML_Syntax.e_tag
  =
  let cache = FStar_Util.smap_create (Prims.parse_int "20")  in
  let rec delta_norm_eff g l =
    let uu____332 = FStar_Util.smap_try_find cache l.FStar_Ident.str  in
    match uu____332 with
    | FStar_Pervasives_Native.Some l1 -> l1
    | FStar_Pervasives_Native.None  ->
        let res =
          let uu____337 =
            FStar_TypeChecker_Env.lookup_effect_abbrev
              g.FStar_Extraction_ML_UEnv.tcenv [FStar_Syntax_Syntax.U_zero] l
             in
          match uu____337 with
          | FStar_Pervasives_Native.None  -> l
          | FStar_Pervasives_Native.Some (uu____348,c) ->
              delta_norm_eff g (FStar_Syntax_Util.comp_effect_name c)
           in
        (FStar_Util.smap_add cache l.FStar_Ident.str res; res)
     in
  fun g  ->
    fun l  ->
      let l1 = delta_norm_eff g l  in
      if FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid
      then FStar_Extraction_ML_Syntax.E_PURE
      else
        if FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GHOST_lid
        then FStar_Extraction_ML_Syntax.E_GHOST
        else
          (let ed_opt =
             FStar_TypeChecker_Env.effect_decl_opt
               g.FStar_Extraction_ML_UEnv.tcenv l1
              in
           match ed_opt with
           | FStar_Pervasives_Native.Some (ed,qualifiers) ->
               let uu____381 =
                 FStar_All.pipe_right qualifiers
                   (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                  in
               if uu____381
               then FStar_Extraction_ML_Syntax.E_PURE
               else FStar_Extraction_ML_Syntax.E_IMPURE
           | FStar_Pervasives_Native.None  ->
               FStar_Extraction_ML_Syntax.E_IMPURE)
  
let rec is_arity :
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t  in
      let uu____400 =
        let uu____401 = FStar_Syntax_Subst.compress t1  in
        uu____401.FStar_Syntax_Syntax.n  in
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
              env.FStar_Extraction_ML_UEnv.tcenv t1
             in
          let uu____504 =
            let uu____505 = FStar_Syntax_Subst.compress t2  in
            uu____505.FStar_Syntax_Syntax.n  in
          (match uu____504 with
           | FStar_Syntax_Syntax.Tm_fvar uu____508 -> false
           | uu____509 -> is_arity env t2)
      | FStar_Syntax_Syntax.Tm_app uu____510 ->
          let uu____525 = FStar_Syntax_Util.head_and_args t1  in
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
  
let rec is_type_aux :
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____729 ->
          let uu____754 =
            let uu____755 = FStar_Syntax_Print.tag_of_term t1  in
            FStar_Util.format1 "Impossible: %s" uu____755  in
          failwith uu____754
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____756 =
            let uu____757 = FStar_Syntax_Print.tag_of_term t1  in
            FStar_Util.format1 "Impossible: %s" uu____757  in
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
          let uu____890 = FStar_Syntax_Subst.open_term bs body  in
          (match uu____890 with | (uu____895,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
          let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
          let uu____912 =
            let uu____917 =
              let uu____918 = FStar_Syntax_Syntax.mk_binder x  in [uu____918]
               in
            FStar_Syntax_Subst.open_term uu____917 body  in
          (match uu____912 with | (uu____919,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_let ((uu____921,lbs),body) ->
          let uu____938 = FStar_Syntax_Subst.open_let_rec lbs body  in
          (match uu____938 with | (uu____945,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_match (uu____951,branches) ->
          (match branches with
           | b::uu____990 ->
               let uu____1035 = FStar_Syntax_Subst.open_branch b  in
               (match uu____1035 with
                | (uu____1036,uu____1037,e) -> is_type_aux env e)
           | uu____1055 -> false)
      | FStar_Syntax_Syntax.Tm_meta (t2,uu____1073) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_app (head1,uu____1079) ->
          is_type_aux env head1
  
let is_type :
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      FStar_Extraction_ML_UEnv.debug env
        (fun uu____1112  ->
           let uu____1113 = FStar_Syntax_Print.tag_of_term t  in
           let uu____1114 = FStar_Syntax_Print.term_to_string t  in
           FStar_Util.print2 "checking is_type (%s) %s\n" uu____1113
             uu____1114);
      (let b = is_type_aux env t  in
       FStar_Extraction_ML_UEnv.debug env
         (fun uu____1120  ->
            if b
            then
              let uu____1121 = FStar_Syntax_Print.term_to_string t  in
              let uu____1122 = FStar_Syntax_Print.tag_of_term t  in
              FStar_Util.print2 "is_type %s (%s)\n" uu____1121 uu____1122
            else
              (let uu____1124 = FStar_Syntax_Print.term_to_string t  in
               let uu____1125 = FStar_Syntax_Print.tag_of_term t  in
               FStar_Util.print2 "not a type %s (%s)\n" uu____1124 uu____1125));
       b)
  
let is_type_binder :
  'Auu____1132 .
    FStar_Extraction_ML_UEnv.env ->
      (FStar_Syntax_Syntax.bv,'Auu____1132) FStar_Pervasives_Native.tuple2 ->
        Prims.bool
  =
  fun env  ->
    fun x  ->
      is_arity env (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
  
let is_constructor : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1153 =
      let uu____1154 = FStar_Syntax_Subst.compress t  in
      uu____1154.FStar_Syntax_Syntax.n  in
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
  
let rec is_fstar_value : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1173 =
      let uu____1174 = FStar_Syntax_Subst.compress t  in
      uu____1174.FStar_Syntax_Syntax.n  in
    match uu____1173 with
    | FStar_Syntax_Syntax.Tm_constant uu____1177 -> true
    | FStar_Syntax_Syntax.Tm_bvar uu____1178 -> true
    | FStar_Syntax_Syntax.Tm_fvar uu____1179 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____1180 -> true
    | FStar_Syntax_Syntax.Tm_app (head1,args) ->
        let uu____1219 = is_constructor head1  in
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
  
let rec is_ml_value : FStar_Extraction_ML_Syntax.mlexpr -> Prims.bool =
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
  
let fresh :
  Prims.string -> (Prims.string,Prims.int) FStar_Pervasives_Native.tuple2 =
  let c = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun x  ->
    FStar_Util.incr c;
    (let uu____1368 =
       let uu____1369 =
         let uu____1370 = FStar_ST.read c  in
         FStar_Util.string_of_int uu____1370  in
       Prims.strcat x uu____1369  in
     let uu____1373 = FStar_ST.read c  in (uu____1368, uu____1373))
  
let normalize_abs : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t0  ->
    let rec aux bs t copt =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_abs (bs',body,copt1) ->
          aux (FStar_List.append bs bs') body copt1
      | uu____1434 ->
          let e' = FStar_Syntax_Util.unascribe t1  in
          let uu____1436 = FStar_Syntax_Util.is_fun e'  in
          if uu____1436
          then aux bs e' copt
          else FStar_Syntax_Util.abs bs e' copt
       in
    aux [] t0 FStar_Pervasives_Native.None
  
let unit_binder : FStar_Syntax_Syntax.binder =
  let uu____1442 =
    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
      FStar_TypeChecker_Common.t_unit
     in
  FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____1442 
let check_pats_for_ite :
  (FStar_Syntax_Syntax.pat,FStar_Syntax_Syntax.term
                             FStar_Pervasives_Native.option,FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.tuple3 Prims.list ->
    (Prims.bool,FStar_Syntax_Syntax.term FStar_Pervasives_Native.option,
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3
  =
  fun l  ->
    let def =
      (false, FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)  in
    if (FStar_List.length l) <> (Prims.parse_int "2")
    then def
    else
      (let uu____1521 = FStar_List.hd l  in
       match uu____1521 with
       | (p1,w1,e1) ->
           let uu____1555 =
             let uu____1564 = FStar_List.tl l  in FStar_List.hd uu____1564
              in
           (match uu____1555 with
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
                 | uu____1638 -> def)))
  
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
          (FStar_Extraction_ML_Syntax.mlexpr,FStar_Extraction_ML_Syntax.e_tag,
            FStar_Extraction_ML_Syntax.mlty) FStar_Pervasives_Native.tuple3
  =
  fun g  ->
    fun e  ->
      fun ty  ->
        fun f  ->
          let e1 =
            let uu____1704 = erasable g f ty  in
            if uu____1704
            then
              let uu____1705 =
                type_leq g ty FStar_Extraction_ML_Syntax.ml_unit_ty  in
              (if uu____1705
               then FStar_Extraction_ML_Syntax.ml_unit
               else
                 FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty)
                   (FStar_Extraction_ML_Syntax.MLE_Coerce
                      (FStar_Extraction_ML_Syntax.ml_unit,
                        FStar_Extraction_ML_Syntax.ml_unit_ty, ty)))
            else e  in
          (e1, f, ty)
  
let eta_expand :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr
  =
  fun t  ->
    fun e  ->
      let uu____1716 = FStar_Extraction_ML_Util.doms_and_cod t  in
      match uu____1716 with
      | (ts,r) ->
          if ts = []
          then e
          else
            (let vs = FStar_List.map (fun uu____1744  -> fresh "a") ts  in
             let vs_ts = FStar_List.zip vs ts  in
             let vs_es =
               let uu____1763 = FStar_List.zip vs ts  in
               FStar_List.map
                 (fun uu____1781  ->
                    match uu____1781 with
                    | (v1,t1) ->
                        FStar_Extraction_ML_Syntax.with_ty t1
                          (FStar_Extraction_ML_Syntax.MLE_Var v1)) uu____1763
                in
             let body =
               FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty r)
                 (FStar_Extraction_ML_Syntax.MLE_App (e, vs_es))
                in
             FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t)
               (FStar_Extraction_ML_Syntax.MLE_Fun (vs_ts, body)))
  
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
          let ty1 = eraseTypeDeep g ty  in
          let uu____1818 =
            type_leq_c g (FStar_Pervasives_Native.Some e) ty1 expect  in
          match uu____1818 with
          | (true ,FStar_Pervasives_Native.Some e') -> e'
          | uu____1828 ->
              (FStar_Extraction_ML_UEnv.debug g
                 (fun uu____1840  ->
                    let uu____1841 =
                      FStar_Extraction_ML_Code.string_of_mlexpr
                        g.FStar_Extraction_ML_UEnv.currentModule e
                       in
                    let uu____1842 =
                      FStar_Extraction_ML_Code.string_of_mlty
                        g.FStar_Extraction_ML_UEnv.currentModule ty1
                       in
                    let uu____1843 =
                      FStar_Extraction_ML_Code.string_of_mlty
                        g.FStar_Extraction_ML_UEnv.currentModule expect
                       in
                    FStar_Util.print3
                      "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n"
                      uu____1841 uu____1842 uu____1843);
               (let uu____1844 =
                  FStar_All.pipe_left
                    (FStar_Extraction_ML_Syntax.with_ty expect)
                    (FStar_Extraction_ML_Syntax.MLE_Coerce (e, ty1, expect))
                   in
                eta_expand expect uu____1844))
  
let bv_as_mlty :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlty
  =
  fun g  ->
    fun bv  ->
      let uu____1853 = FStar_Extraction_ML_UEnv.lookup_bv g bv  in
      match uu____1853 with
      | FStar_Util.Inl (uu____1854,t) -> t
      | uu____1868 -> FStar_Extraction_ML_Syntax.MLTY_Top
  
let rec term_as_mlty :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlty
  =
  fun g  ->
    fun t0  ->
      let rec is_top_ty t =
        match t with
        | FStar_Extraction_ML_Syntax.MLTY_Top  -> true
        | FStar_Extraction_ML_Syntax.MLTY_Named uu____1911 ->
            let uu____1918 = FStar_Extraction_ML_Util.udelta_unfold g t  in
            (match uu____1918 with
             | FStar_Pervasives_Native.None  -> false
             | FStar_Pervasives_Native.Some t1 -> is_top_ty t1)
        | uu____1922 -> false  in
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
      let uu____1925 = is_top_ty mlt  in
      if uu____1925
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
            g.FStar_Extraction_ML_UEnv.tcenv t0
           in
        term_as_mlty' g t1
      else mlt

and term_as_mlty' :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlty
  =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_bvar uu____1931 ->
          let uu____1932 =
            let uu____1933 = FStar_Syntax_Print.term_to_string t1  in
            FStar_Util.format1 "Impossible: Unexpected term %s" uu____1933
             in
          failwith uu____1932
      | FStar_Syntax_Syntax.Tm_delayed uu____1934 ->
          let uu____1959 =
            let uu____1960 = FStar_Syntax_Print.term_to_string t1  in
            FStar_Util.format1 "Impossible: Unexpected term %s" uu____1960
             in
          failwith uu____1959
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____1961 =
            let uu____1962 = FStar_Syntax_Print.term_to_string t1  in
            FStar_Util.format1 "Impossible: Unexpected term %s" uu____1962
             in
          failwith uu____1961
      | FStar_Syntax_Syntax.Tm_constant uu____1963 ->
          FStar_Extraction_ML_UEnv.unknownType
      | FStar_Syntax_Syntax.Tm_uvar uu____1964 ->
          FStar_Extraction_ML_UEnv.unknownType
      | FStar_Syntax_Syntax.Tm_meta (t2,uu____1982) -> term_as_mlty' env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____1987;
             FStar_Syntax_Syntax.index = uu____1988;
             FStar_Syntax_Syntax.sort = t2;_},uu____1990)
          -> term_as_mlty' env t2
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____1998) -> term_as_mlty' env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____2004,uu____2005) ->
          term_as_mlty' env t2
      | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
      | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv []
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____2072 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____2072 with
           | (bs1,c1) ->
               let uu____2079 = binders_as_ml_binders env bs1  in
               (match uu____2079 with
                | (mlbs,env1) ->
                    let t_ret =
                      let eff =
                        FStar_TypeChecker_Env.norm_eff_name
                          env1.FStar_Extraction_ML_UEnv.tcenv
                          (FStar_Syntax_Util.comp_effect_name c1)
                         in
                      let uu____2106 =
                        let uu____2113 =
                          FStar_TypeChecker_Env.effect_decl_opt
                            env1.FStar_Extraction_ML_UEnv.tcenv eff
                           in
                        FStar_Util.must uu____2113  in
                      match uu____2106 with
                      | (ed,qualifiers) ->
                          let uu____2134 =
                            FStar_All.pipe_right qualifiers
                              (FStar_List.contains
                                 FStar_Syntax_Syntax.Reifiable)
                             in
                          if uu____2134
                          then
                            let t2 =
                              FStar_TypeChecker_Env.reify_comp
                                env1.FStar_Extraction_ML_UEnv.tcenv c1
                                FStar_Syntax_Syntax.U_unknown
                               in
                            let res = term_as_mlty' env1 t2  in res
                          else
                            term_as_mlty' env1
                              (FStar_Syntax_Util.comp_result c1)
                       in
                    let erase1 =
                      effect_as_etag env1
                        (FStar_Syntax_Util.comp_effect_name c1)
                       in
                    let uu____2141 =
                      FStar_List.fold_right
                        (fun uu____2160  ->
                           fun uu____2161  ->
                             match (uu____2160, uu____2161) with
                             | ((uu____2182,t2),(tag,t')) ->
                                 (FStar_Extraction_ML_Syntax.E_PURE,
                                   (FStar_Extraction_ML_Syntax.MLTY_Fun
                                      (t2, tag, t')))) mlbs (erase1, t_ret)
                       in
                    (match uu____2141 with | (uu____2194,t2) -> t2)))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let res =
            let uu____2219 =
              let uu____2220 = FStar_Syntax_Util.un_uinst head1  in
              uu____2220.FStar_Syntax_Syntax.n  in
            match uu____2219 with
            | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
            | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv args
            | FStar_Syntax_Syntax.Tm_app (head2,args') ->
                let uu____2247 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app
                       (head2, (FStar_List.append args' args)))
                    FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   in
                term_as_mlty' env uu____2247
            | uu____2264 -> FStar_Extraction_ML_UEnv.unknownType  in
          res
      | FStar_Syntax_Syntax.Tm_abs (bs,ty,uu____2267) ->
          let uu____2288 = FStar_Syntax_Subst.open_term bs ty  in
          (match uu____2288 with
           | (bs1,ty1) ->
               let uu____2295 = binders_as_ml_binders env bs1  in
               (match uu____2295 with | (bts,env1) -> term_as_mlty' env1 ty1))
      | FStar_Syntax_Syntax.Tm_type uu____2320 ->
          FStar_Extraction_ML_UEnv.unknownType
      | FStar_Syntax_Syntax.Tm_let uu____2321 ->
          FStar_Extraction_ML_UEnv.unknownType
      | FStar_Syntax_Syntax.Tm_match uu____2334 ->
          FStar_Extraction_ML_UEnv.unknownType

and arg_as_mlty :
  FStar_Extraction_ML_UEnv.env ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 -> FStar_Extraction_ML_Syntax.mlty
  =
  fun g  ->
    fun uu____2358  ->
      match uu____2358 with
      | (a,uu____2364) ->
          let uu____2365 = is_type g a  in
          if uu____2365
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
        let uu____2370 =
          let uu____2383 =
            FStar_TypeChecker_Env.lookup_lid g.FStar_Extraction_ML_UEnv.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____2383 with
          | ((uu____2404,fvty),uu____2406) ->
              let fvty1 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Normalize.UnfoldUntil
                     FStar_Syntax_Syntax.Delta_constant]
                  g.FStar_Extraction_ML_UEnv.tcenv fvty
                 in
              FStar_Syntax_Util.arrow_formals fvty1
           in
        match uu____2370 with
        | (formals,uu____2413) ->
            let mlargs = FStar_List.map (arg_as_mlty g) args  in
            let mlargs1 =
              let n_args = FStar_List.length args  in
              if (FStar_List.length formals) > n_args
              then
                let uu____2457 = FStar_Util.first_N n_args formals  in
                match uu____2457 with
                | (uu____2484,rest) ->
                    let uu____2510 =
                      FStar_List.map
                        (fun uu____2518  ->
                           FStar_Extraction_ML_UEnv.erasedContent) rest
                       in
                    FStar_List.append mlargs uu____2510
              else mlargs  in
            let nm =
              let uu____2525 =
                FStar_Extraction_ML_UEnv.maybe_mangle_type_projector g fv  in
              match uu____2525 with
              | FStar_Pervasives_Native.Some p -> p
              | FStar_Pervasives_Native.None  ->
                  FStar_Extraction_ML_Syntax.mlpath_of_lident
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            FStar_Extraction_ML_Syntax.MLTY_Named (mlargs1, nm)

and binders_as_ml_binders :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.binders ->
      ((FStar_Extraction_ML_Syntax.mlident,FStar_Extraction_ML_Syntax.mlty)
         FStar_Pervasives_Native.tuple2 Prims.list,FStar_Extraction_ML_UEnv.env)
        FStar_Pervasives_Native.tuple2
  =
  fun g  ->
    fun bs  ->
      let uu____2543 =
        FStar_All.pipe_right bs
          (FStar_List.fold_left
             (fun uu____2598  ->
                fun b  ->
                  match uu____2598 with
                  | (ml_bs,env) ->
                      let uu____2654 = is_type_binder g b  in
                      if uu____2654
                      then
                        let b1 = FStar_Pervasives_Native.fst b  in
                        let env1 =
                          FStar_Extraction_ML_UEnv.extend_ty env b1
                            (FStar_Pervasives_Native.Some
                               FStar_Extraction_ML_Syntax.MLTY_Top)
                           in
                        let ml_b =
                          let uu____2680 =
                            FStar_Extraction_ML_UEnv.bv_as_ml_termvar b1  in
                          (uu____2680, FStar_Extraction_ML_Syntax.ml_unit_ty)
                           in
                        ((ml_b :: ml_bs), env1)
                      else
                        (let b1 = FStar_Pervasives_Native.fst b  in
                         let t = term_as_mlty env b1.FStar_Syntax_Syntax.sort
                            in
                         let uu____2710 =
                           FStar_Extraction_ML_UEnv.extend_bv env b1 
                             ([], t) false false false
                            in
                         match uu____2710 with
                         | (env1,b2) ->
                             let ml_b =
                               let uu____2742 =
                                 FStar_Extraction_ML_UEnv.removeTick b2  in
                               (uu____2742, t)  in
                             ((ml_b :: ml_bs), env1))) ([], g))
         in
      match uu____2543 with | (ml_bs,env) -> ((FStar_List.rev ml_bs), env)

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
      | (FStar_Extraction_ML_Syntax.MLE_Seq es1,uu____2852) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (FStar_List.append es1 [e2])
      | (uu____2855,FStar_Extraction_ML_Syntax.MLE_Seq es2) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (e1 :: es2)
      | uu____2859 -> FStar_Extraction_ML_Syntax.MLE_Seq [e1; e2]
  
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
                    | uu____2891 when
                        (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
                          =
                          FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr
                        -> body.FStar_Extraction_ML_Syntax.expr
                    | uu____2892 ->
                        mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def
                          body)
             | uu____2893 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body))
        | uu____2896 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body)
  
let resugar_pat :
  FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option ->
    FStar_Extraction_ML_Syntax.mlpattern ->
      FStar_Extraction_ML_Syntax.mlpattern
  =
  fun q  ->
    fun p  ->
      match p with
      | FStar_Extraction_ML_Syntax.MLP_CTor (d,pats) ->
          let uu____2915 = FStar_Extraction_ML_Util.is_xtuple d  in
          (match uu____2915 with
           | FStar_Pervasives_Native.Some n1 ->
               FStar_Extraction_ML_Syntax.MLP_Tuple pats
           | uu____2919 ->
               (match q with
                | FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Record_ctor (ty,fns)) ->
                    let path =
                      FStar_List.map FStar_Ident.text_of_id ty.FStar_Ident.ns
                       in
                    let fs = record_fields fns pats  in
                    FStar_Extraction_ML_Syntax.MLP_Record (path, fs)
                | uu____2946 -> p))
      | uu____2949 -> p
  
let rec extract_one_pat :
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
                let ok = type_leq g t t'  in
                (if Prims.op_Negation ok
                 then
                   FStar_Extraction_ML_UEnv.debug g
                     (fun uu____3008  ->
                        let uu____3009 =
                          FStar_Extraction_ML_Code.string_of_mlty
                            g.FStar_Extraction_ML_UEnv.currentModule t'
                           in
                        let uu____3010 =
                          FStar_Extraction_ML_Code.string_of_mlty
                            g.FStar_Extraction_ML_UEnv.currentModule t
                           in
                        FStar_Util.print2
                          "Expected pattern type %s; got pattern type %s\n"
                          uu____3009 uu____3010)
                 else ();
                 ok)
             in
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int
              (c,FStar_Pervasives_Native.None )) ->
              let i = FStar_Const.Const_int (c, FStar_Pervasives_Native.None)
                 in
              let x = FStar_Extraction_ML_Syntax.gensym ()  in
              let when_clause =
                let uu____3050 =
                  let uu____3051 =
                    let uu____3058 =
                      let uu____3061 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.ml_int_ty)
                          (FStar_Extraction_ML_Syntax.MLE_Var x)
                         in
                      let uu____3062 =
                        let uu____3065 =
                          let uu____3066 =
                            let uu____3067 =
                              FStar_Extraction_ML_Util.mlconst_of_const'
                                p.FStar_Syntax_Syntax.p i
                               in
                            FStar_All.pipe_left
                              (fun _0_41  ->
                                 FStar_Extraction_ML_Syntax.MLE_Const _0_41)
                              uu____3067
                             in
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty
                               FStar_Extraction_ML_Syntax.ml_int_ty)
                            uu____3066
                           in
                        [uu____3065]  in
                      uu____3061 :: uu____3062  in
                    (FStar_Extraction_ML_Util.prims_op_equality, uu____3058)
                     in
                  FStar_Extraction_ML_Syntax.MLE_App uu____3051  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     FStar_Extraction_ML_Syntax.ml_bool_ty) uu____3050
                 in
              let uu____3070 = ok FStar_Extraction_ML_Syntax.ml_int_ty  in
              (g,
                (FStar_Pervasives_Native.Some
                   ((FStar_Extraction_ML_Syntax.MLP_Var x), [when_clause])),
                uu____3070)
          | FStar_Syntax_Syntax.Pat_constant s ->
              let t =
                FStar_TypeChecker_TcTerm.tc_constant FStar_Range.dummyRange s
                 in
              let mlty = term_as_mlty g t  in
              let uu____3090 =
                let uu____3099 =
                  let uu____3106 =
                    let uu____3107 =
                      FStar_Extraction_ML_Util.mlconst_of_const'
                        p.FStar_Syntax_Syntax.p s
                       in
                    FStar_Extraction_ML_Syntax.MLP_Const uu____3107  in
                  (uu____3106, [])  in
                FStar_Pervasives_Native.Some uu____3099  in
              let uu____3116 = ok mlty  in (g, uu____3090, uu____3116)
          | FStar_Syntax_Syntax.Pat_var x ->
              let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort  in
              let uu____3127 =
                FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false false
                  imp
                 in
              (match uu____3127 with
               | (g1,x1) ->
                   let uu____3150 = ok mlty  in
                   (g1,
                     (if imp
                      then FStar_Pervasives_Native.None
                      else
                        FStar_Pervasives_Native.Some
                          ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                     uu____3150))
          | FStar_Syntax_Syntax.Pat_wild x ->
              let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort  in
              let uu____3184 =
                FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false false
                  imp
                 in
              (match uu____3184 with
               | (g1,x1) ->
                   let uu____3207 = ok mlty  in
                   (g1,
                     (if imp
                      then FStar_Pervasives_Native.None
                      else
                        FStar_Pervasives_Native.Some
                          ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                     uu____3207))
          | FStar_Syntax_Syntax.Pat_dot_term uu____3239 ->
              (g, FStar_Pervasives_Native.None, true)
          | FStar_Syntax_Syntax.Pat_cons (f,pats) ->
              let uu____3278 =
                let uu____3283 = FStar_Extraction_ML_UEnv.lookup_fv g f  in
                match uu____3283 with
                | FStar_Util.Inr
                    (uu____3288,{
                                  FStar_Extraction_ML_Syntax.expr =
                                    FStar_Extraction_ML_Syntax.MLE_Name n1;
                                  FStar_Extraction_ML_Syntax.mlty =
                                    uu____3290;
                                  FStar_Extraction_ML_Syntax.loc = uu____3291;_},ttys,uu____3293)
                    -> (n1, ttys)
                | uu____3306 -> failwith "Expected a constructor"  in
              (match uu____3278 with
               | (d,tys) ->
                   let nTyVars =
                     FStar_List.length (FStar_Pervasives_Native.fst tys)  in
                   let uu____3328 = FStar_Util.first_N nTyVars pats  in
                   (match uu____3328 with
                    | (tysVarPats,restPats) ->
                        let f_ty_opt =
                          try
                            let mlty_args =
                              FStar_All.pipe_right tysVarPats
                                (FStar_List.map
                                   (fun uu____3461  ->
                                      match uu____3461 with
                                      | (p1,uu____3469) ->
                                          (match p1.FStar_Syntax_Syntax.v
                                           with
                                           | FStar_Syntax_Syntax.Pat_dot_term
                                               (uu____3474,t) ->
                                               term_as_mlty g t
                                           | uu____3480 ->
                                               (FStar_Extraction_ML_UEnv.debug
                                                  g
                                                  (fun uu____3484  ->
                                                     let uu____3485 =
                                                       FStar_Syntax_Print.pat_to_string
                                                         p1
                                                        in
                                                     FStar_Util.print1
                                                       "Pattern %s is not extractable"
                                                       uu____3485);
                                                raise Un_extractable))))
                               in
                            let f_ty =
                              FStar_Extraction_ML_Util.subst tys mlty_args
                               in
                            let uu____3487 =
                              FStar_Extraction_ML_Util.uncurry_mlty_fun f_ty
                               in
                            FStar_Pervasives_Native.Some uu____3487
                          with
                          | Un_extractable  -> FStar_Pervasives_Native.None
                           in
                        let uu____3516 =
                          FStar_Util.fold_map
                            (fun g1  ->
                               fun uu____3552  ->
                                 match uu____3552 with
                                 | (p1,imp1) ->
                                     let uu____3571 =
                                       extract_one_pat true g1 p1
                                         FStar_Pervasives_Native.None
                                        in
                                     (match uu____3571 with
                                      | (g2,p2,uu____3600) -> (g2, p2))) g
                            tysVarPats
                           in
                        (match uu____3516 with
                         | (g1,tyMLPats) ->
                             let uu____3661 =
                               FStar_Util.fold_map
                                 (fun uu____3725  ->
                                    fun uu____3726  ->
                                      match (uu____3725, uu____3726) with
                                      | ((g2,f_ty_opt1),(p1,imp1)) ->
                                          let uu____3819 =
                                            match f_ty_opt1 with
                                            | FStar_Pervasives_Native.Some
                                                (hd1::rest,res) ->
                                                ((FStar_Pervasives_Native.Some
                                                    (rest, res)),
                                                  (FStar_Pervasives_Native.Some
                                                     hd1))
                                            | uu____3879 ->
                                                (FStar_Pervasives_Native.None,
                                                  FStar_Pervasives_Native.None)
                                             in
                                          (match uu____3819 with
                                           | (f_ty_opt2,expected_ty) ->
                                               let uu____3950 =
                                                 extract_one_pat false g2 p1
                                                   expected_ty
                                                  in
                                               (match uu____3950 with
                                                | (g3,p2,uu____3991) ->
                                                    ((g3, f_ty_opt2), p2))))
                                 (g1, f_ty_opt) restPats
                                in
                             (match uu____3661 with
                              | ((g2,f_ty_opt1),restMLPats) ->
                                  let uu____4109 =
                                    let uu____4120 =
                                      FStar_All.pipe_right
                                        (FStar_List.append tyMLPats
                                           restMLPats)
                                        (FStar_List.collect
                                           (fun uu___139_4171  ->
                                              match uu___139_4171 with
                                              | FStar_Pervasives_Native.Some
                                                  x -> [x]
                                              | uu____4213 -> []))
                                       in
                                    FStar_All.pipe_right uu____4120
                                      FStar_List.split
                                     in
                                  (match uu____4109 with
                                   | (mlPats,when_clauses) ->
                                       let pat_ty_compat =
                                         match f_ty_opt1 with
                                         | FStar_Pervasives_Native.Some
                                             ([],t) -> ok t
                                         | uu____4286 -> false  in
                                       let uu____4295 =
                                         let uu____4304 =
                                           let uu____4311 =
                                             resugar_pat
                                               f.FStar_Syntax_Syntax.fv_qual
                                               (FStar_Extraction_ML_Syntax.MLP_CTor
                                                  (d, mlPats))
                                              in
                                           let uu____4314 =
                                             FStar_All.pipe_right
                                               when_clauses
                                               FStar_List.flatten
                                              in
                                           (uu____4311, uu____4314)  in
                                         FStar_Pervasives_Native.Some
                                           uu____4304
                                          in
                                       (g2, uu____4295, pat_ty_compat))))))
  
let extract_pat :
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
          let uu____4405 = extract_one_pat false g1 p1 expected_t1  in
          match uu____4405 with
          | (g2,FStar_Pervasives_Native.Some (x,v1),b) -> (g2, (x, v1), b)
          | uu____4462 -> failwith "Impossible: Unable to translate pattern"
           in
        let mk_when_clause whens =
          match whens with
          | [] -> FStar_Pervasives_Native.None
          | hd1::tl1 ->
              let uu____4505 =
                FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd1 tl1
                 in
              FStar_Pervasives_Native.Some uu____4505
           in
        let uu____4506 =
          extract_one_pat1 g p (FStar_Pervasives_Native.Some expected_t)  in
        match uu____4506 with
        | (g1,(p1,whens),b) ->
            let when_clause = mk_when_clause whens  in
            (g1, [(p1, when_clause)], b)
  
let maybe_eta_data_and_project_record :
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
            | FStar_Extraction_ML_Syntax.MLTY_Fun (t0,uu____4648,t1) ->
                let x = FStar_Extraction_ML_Syntax.gensym ()  in
                let uu____4651 =
                  let uu____4662 =
                    let uu____4671 =
                      FStar_All.pipe_left
                        (FStar_Extraction_ML_Syntax.with_ty t0)
                        (FStar_Extraction_ML_Syntax.MLE_Var x)
                       in
                    ((x, t0), uu____4671)  in
                  uu____4662 :: more_args  in
                eta_args uu____4651 t1
            | FStar_Extraction_ML_Syntax.MLTY_Named (uu____4684,uu____4685)
                -> ((FStar_List.rev more_args), t)
            | uu____4708 -> failwith "Impossible: Head type is not an arrow"
             in
          let as_record qual1 e =
            match ((e.FStar_Extraction_ML_Syntax.expr), qual1) with
            | (FStar_Extraction_ML_Syntax.MLE_CTor
               (uu____4736,args),FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Record_ctor (tyname,fields))) ->
                let path =
                  FStar_List.map FStar_Ident.text_of_id tyname.FStar_Ident.ns
                   in
                let fields1 = record_fields fields args  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     e.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_Record (path, fields1))
            | uu____4768 -> e  in
          let resugar_and_maybe_eta qual1 e =
            let uu____4786 = eta_args [] residualType  in
            match uu____4786 with
            | (eargs,tres) ->
                (match eargs with
                 | [] ->
                     let uu____4839 = as_record qual1 e  in
                     FStar_Extraction_ML_Util.resugar_exp uu____4839
                 | uu____4840 ->
                     let uu____4851 = FStar_List.unzip eargs  in
                     (match uu____4851 with
                      | (binders,eargs1) ->
                          (match e.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_CTor (head1,args)
                               ->
                               let body =
                                 let uu____4893 =
                                   let uu____4894 =
                                     FStar_All.pipe_left
                                       (FStar_Extraction_ML_Syntax.with_ty
                                          tres)
                                       (FStar_Extraction_ML_Syntax.MLE_CTor
                                          (head1,
                                            (FStar_List.append args eargs1)))
                                      in
                                   FStar_All.pipe_left (as_record qual1)
                                     uu____4894
                                    in
                                 FStar_All.pipe_left
                                   FStar_Extraction_ML_Util.resugar_exp
                                   uu____4893
                                  in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    e.FStar_Extraction_ML_Syntax.mlty)
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    (binders, body))
                           | uu____4903 ->
                               failwith "Impossible: Not a constructor")))
             in
          match ((mlAppExpr.FStar_Extraction_ML_Syntax.expr), qual) with
          | (uu____4906,FStar_Pervasives_Native.None ) -> mlAppExpr
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____4910;
                FStar_Extraction_ML_Syntax.loc = uu____4911;_},mle::args),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_projector (constrname,f))) ->
              let f1 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append constrname.FStar_Ident.ns [f])
                 in
              let fn = FStar_Extraction_ML_Util.mlpath_of_lid f1  in
              let proj = FStar_Extraction_ML_Syntax.MLE_Proj (mle, fn)  in
              let e =
                match args with
                | [] -> proj
                | uu____4938 ->
                    let uu____4941 =
                      let uu____4948 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj
                         in
                      (uu____4948, args)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____4941
                 in
              FStar_Extraction_ML_Syntax.with_ty
                mlAppExpr.FStar_Extraction_ML_Syntax.mlty e
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____4952;
                FStar_Extraction_ML_Syntax.loc = uu____4953;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____4961 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____4961
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____4965;
                FStar_Extraction_ML_Syntax.loc = uu____4966;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____4968)) ->
              let uu____4981 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____4981
          | (FStar_Extraction_ML_Syntax.MLE_Name
             mlp,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor
             )) ->
              let uu____4987 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____4987
          | (FStar_Extraction_ML_Syntax.MLE_Name
             mlp,FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____4991)) ->
              let uu____5000 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5000
          | uu____5003 -> mlAppExpr
  
let maybe_downgrade_eff :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.e_tag ->
      FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.e_tag
  =
  fun g  ->
    fun f  ->
      fun t  ->
        let uu____5022 =
          (f = FStar_Extraction_ML_Syntax.E_GHOST) &&
            (type_leq g t FStar_Extraction_ML_Syntax.ml_unit_ty)
           in
        if uu____5022 then FStar_Extraction_ML_Syntax.E_PURE else f
  
let rec term_as_mlexpr :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Extraction_ML_Syntax.mlexpr,FStar_Extraction_ML_Syntax.e_tag,
        FStar_Extraction_ML_Syntax.mlty) FStar_Pervasives_Native.tuple3
  =
  fun g  ->
    fun t  ->
      let uu____5076 = term_as_mlexpr' g t  in
      match uu____5076 with
      | (e,tag,ty) ->
          let tag1 = maybe_downgrade_eff g tag ty  in
          (FStar_Extraction_ML_UEnv.debug g
             (fun u  ->
                let uu____5097 =
                  let uu____5098 = FStar_Syntax_Print.tag_of_term t  in
                  let uu____5099 = FStar_Syntax_Print.term_to_string t  in
                  let uu____5100 =
                    FStar_Extraction_ML_Code.string_of_mlty
                      g.FStar_Extraction_ML_UEnv.currentModule ty
                     in
                  FStar_Util.format4
                    "term_as_mlexpr (%s) :  %s has ML type %s and effect %s\n"
                    uu____5098 uu____5099 uu____5100
                    (FStar_Extraction_ML_Util.eff_to_string tag1)
                   in
                FStar_Util.print_string uu____5097);
           erase g e ty tag1)

and check_term_as_mlexpr :
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
          let uu____5109 = check_term_as_mlexpr' g t f ty  in
          match uu____5109 with
          | (e,t1) ->
              let uu____5120 = erase g e t1 f  in
              (match uu____5120 with | (r,uu____5132,t2) -> (r, t2))

and check_term_as_mlexpr' :
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
          let uu____5142 = term_as_mlexpr g e0  in
          match uu____5142 with
          | (e,tag,t) ->
              let tag1 = maybe_downgrade_eff g tag t  in
              if FStar_Extraction_ML_Util.eff_leq tag1 f
              then
                let uu____5161 = maybe_coerce g e t ty  in (uu____5161, ty)
              else err_unexpected_eff e0 f tag1

and term_as_mlexpr' :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Extraction_ML_Syntax.mlexpr,FStar_Extraction_ML_Syntax.e_tag,
        FStar_Extraction_ML_Syntax.mlty) FStar_Pervasives_Native.tuple3
  =
  fun g  ->
    fun top  ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u  ->
           let uu____5179 =
             let uu____5180 =
               FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos  in
             let uu____5181 = FStar_Syntax_Print.tag_of_term top  in
             let uu____5182 = FStar_Syntax_Print.term_to_string top  in
             FStar_Util.format3 "%s: term_as_mlexpr' (%s) :  %s \n"
               uu____5180 uu____5181 uu____5182
              in
           FStar_Util.print_string uu____5179);
      (let t = FStar_Syntax_Subst.compress top  in
       match t.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____5190 =
             let uu____5191 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5191
              in
           failwith uu____5190
       | FStar_Syntax_Syntax.Tm_delayed uu____5198 ->
           let uu____5223 =
             let uu____5224 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5224
              in
           failwith uu____5223
       | FStar_Syntax_Syntax.Tm_uvar uu____5231 ->
           let uu____5248 =
             let uu____5249 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5249
              in
           failwith uu____5248
       | FStar_Syntax_Syntax.Tm_bvar uu____5256 ->
           let uu____5257 =
             let uu____5258 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5258
              in
           failwith uu____5257
       | FStar_Syntax_Syntax.Tm_type uu____5265 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_refine uu____5266 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_arrow uu____5273 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Mutable_alloc ))
           ->
           let uu____5291 = term_as_mlexpr' g t1  in
           (match uu____5291 with
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
            | uu____5337 -> failwith "impossible")
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_monadic (m,uu____5352)) ->
           let t2 = FStar_Syntax_Subst.compress t1  in
           (match t2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) when
                FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname ->
                let uu____5382 =
                  let uu____5389 =
                    FStar_TypeChecker_Env.effect_decl_opt
                      g.FStar_Extraction_ML_UEnv.tcenv m
                     in
                  FStar_Util.must uu____5389  in
                (match uu____5382 with
                 | (ed,qualifiers) ->
                     let uu____5416 =
                       let uu____5417 =
                         FStar_All.pipe_right qualifiers
                           (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                          in
                       FStar_All.pipe_right uu____5417 Prims.op_Negation  in
                     if uu____5416
                     then term_as_mlexpr' g t2
                     else
                       failwith
                         "This should not happen (should have been handled at Tm_abs level)")
            | uu____5433 -> term_as_mlexpr' g t2)
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____5435) -> term_as_mlexpr' g t1
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____5441) -> term_as_mlexpr' g t1
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____5447 =
             FStar_TypeChecker_TcTerm.type_of_tot_term
               g.FStar_Extraction_ML_UEnv.tcenv t
              in
           (match uu____5447 with
            | (uu____5460,ty,uu____5462) ->
                let ml_ty = term_as_mlty g ty  in
                let uu____5464 =
                  let uu____5465 =
                    let uu____5466 =
                      FStar_Extraction_ML_Util.mlconst_of_const'
                        t.FStar_Syntax_Syntax.pos c
                       in
                    FStar_All.pipe_left
                      (fun _0_42  ->
                         FStar_Extraction_ML_Syntax.MLE_Const _0_42)
                      uu____5466
                     in
                  FStar_Extraction_ML_Syntax.with_ty ml_ty uu____5465  in
                (uu____5464, FStar_Extraction_ML_Syntax.E_PURE, ml_ty))
       | FStar_Syntax_Syntax.Tm_name uu____5467 ->
           let uu____5468 = is_type g t  in
           if uu____5468
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____5476 = FStar_Extraction_ML_UEnv.lookup_term g t  in
              match uu____5476 with
              | (FStar_Util.Inl uu____5489,uu____5490) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | (FStar_Util.Inr (uu____5527,x,mltys,uu____5530),qual) ->
                  (match mltys with
                   | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                       ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | ([],t1) ->
                       let uu____5576 =
                         maybe_eta_data_and_project_record g qual t1 x  in
                       (uu____5576, FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | uu____5577 -> err_uninst g t mltys t))
       | FStar_Syntax_Syntax.Tm_fvar uu____5584 ->
           let uu____5585 = is_type g t  in
           if uu____5585
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____5593 = FStar_Extraction_ML_UEnv.lookup_term g t  in
              match uu____5593 with
              | (FStar_Util.Inl uu____5606,uu____5607) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | (FStar_Util.Inr (uu____5644,x,mltys,uu____5647),qual) ->
                  (match mltys with
                   | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                       ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | ([],t1) ->
                       let uu____5693 =
                         maybe_eta_data_and_project_record g qual t1 x  in
                       (uu____5693, FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | uu____5694 -> err_uninst g t mltys t))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,copt) ->
           let uu____5724 = FStar_Syntax_Subst.open_term bs body  in
           (match uu____5724 with
            | (bs1,body1) ->
                let uu____5737 = binders_as_ml_binders g bs1  in
                (match uu____5737 with
                 | (ml_bs,env) ->
                     let body2 =
                       match copt with
                       | FStar_Pervasives_Native.Some c ->
                           let uu____5770 =
                             FStar_TypeChecker_Env.is_reifiable
                               env.FStar_Extraction_ML_UEnv.tcenv c
                              in
                           if uu____5770
                           then
                             FStar_TypeChecker_Util.reify_body
                               env.FStar_Extraction_ML_UEnv.tcenv body1
                           else body1
                       | FStar_Pervasives_Native.None  ->
                           (FStar_Extraction_ML_UEnv.debug g
                              (fun uu____5775  ->
                                 let uu____5776 =
                                   FStar_Syntax_Print.term_to_string body1
                                    in
                                 FStar_Util.print1
                                   "No computation type for: %s\n" uu____5776);
                            body1)
                        in
                     let uu____5777 = term_as_mlexpr env body2  in
                     (match uu____5777 with
                      | (ml_body,f,t1) ->
                          let uu____5793 =
                            FStar_List.fold_right
                              (fun uu____5812  ->
                                 fun uu____5813  ->
                                   match (uu____5812, uu____5813) with
                                   | ((uu____5834,targ),(f1,t2)) ->
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         (FStar_Extraction_ML_Syntax.MLTY_Fun
                                            (targ, f1, t2)))) ml_bs (f, t1)
                             in
                          (match uu____5793 with
                           | (f1,tfun) ->
                               let uu____5854 =
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty tfun)
                                   (FStar_Extraction_ML_Syntax.MLE_Fun
                                      (ml_bs, ml_body))
                                  in
                               (uu____5854, f1, tfun)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____5861);
              FStar_Syntax_Syntax.pos = uu____5862;
              FStar_Syntax_Syntax.vars = uu____5863;_},uu____5864)
           -> failwith "Unreachable? Tm_app Const_reflect"
       | FStar_Syntax_Syntax.Tm_app (head1,uu____5892::(v1,uu____5894)::[])
           when (FStar_Syntax_Util.is_fstar_tactics_embed head1) && false ->
           let uu____5935 =
             let uu____5938 = FStar_Syntax_Print.term_to_string v1  in
             FStar_Util.format2 "Trying to extract a quotation of %s"
               uu____5938
              in
           let s =
             let uu____5940 =
               let uu____5941 =
                 let uu____5942 =
                   let uu____5945 = FStar_Util.marshal v1  in
                   FStar_Util.bytes_of_string uu____5945  in
                 FStar_Extraction_ML_Syntax.MLC_Bytes uu____5942  in
               FStar_Extraction_ML_Syntax.MLE_Const uu____5941  in
             FStar_Extraction_ML_Syntax.with_ty
               FStar_Extraction_ML_Syntax.ml_string_ty uu____5940
              in
           let zero1 =
             FStar_Extraction_ML_Syntax.with_ty
               FStar_Extraction_ML_Syntax.ml_int_ty
               (FStar_Extraction_ML_Syntax.MLE_Const
                  (FStar_Extraction_ML_Syntax.MLC_Int
                     ("0", FStar_Pervasives_Native.None)))
              in
           let term_ty =
             let uu____5960 =
               FStar_Syntax_Syntax.fvar
                 FStar_Parser_Const.fstar_syntax_syntax_term
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None
                in
             term_as_mlty g uu____5960  in
           let marshal_from_string =
             let string_to_term_ty =
               FStar_Extraction_ML_Syntax.MLTY_Fun
                 (FStar_Extraction_ML_Syntax.ml_string_ty,
                   FStar_Extraction_ML_Syntax.E_PURE, term_ty)
                in
             FStar_Extraction_ML_Syntax.with_ty string_to_term_ty
               (FStar_Extraction_ML_Syntax.MLE_Name
                  (["Marshal"], "from_string"))
              in
           let uu____5965 =
             FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty term_ty)
               (FStar_Extraction_ML_Syntax.MLE_App
                  (marshal_from_string, [s; zero1]))
              in
           (uu____5965, FStar_Extraction_ML_Syntax.E_PURE, term_ty)
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let is_total rc =
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_Tot_lid)
               ||
               (FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
                  (FStar_List.existsb
                     (fun uu___140_5997  ->
                        match uu___140_5997 with
                        | FStar_Syntax_Syntax.TOTAL  -> true
                        | uu____5998 -> false)))
              in
           let uu____5999 =
             let uu____6004 =
               let uu____6005 = FStar_Syntax_Subst.compress head1  in
               uu____6005.FStar_Syntax_Syntax.n  in
             ((head1.FStar_Syntax_Syntax.n), uu____6004)  in
           (match uu____5999 with
            | (FStar_Syntax_Syntax.Tm_uvar uu____6014,uu____6015) ->
                let t1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.Iota;
                    FStar_TypeChecker_Normalize.Zeta;
                    FStar_TypeChecker_Normalize.EraseUniverses;
                    FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                    g.FStar_Extraction_ML_UEnv.tcenv t
                   in
                term_as_mlexpr' g t1
            | (uu____6033,FStar_Syntax_Syntax.Tm_abs
               (bs,uu____6035,FStar_Pervasives_Native.Some rc)) when
                is_total rc ->
                let t1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.Iota;
                    FStar_TypeChecker_Normalize.Zeta;
                    FStar_TypeChecker_Normalize.EraseUniverses;
                    FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                    g.FStar_Extraction_ML_UEnv.tcenv t
                   in
                term_as_mlexpr' g t1
            | (uu____6056,FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_reify )) ->
                let e =
                  let uu____6058 = FStar_List.hd args  in
                  FStar_TypeChecker_Util.reify_body_with_arg
                    g.FStar_Extraction_ML_UEnv.tcenv head1 uu____6058
                   in
                let tm =
                  let uu____6068 =
                    let uu____6069 = FStar_TypeChecker_Util.remove_reify e
                       in
                    let uu____6070 = FStar_List.tl args  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____6069 uu____6070  in
                  uu____6068 FStar_Pervasives_Native.None
                    t.FStar_Syntax_Syntax.pos
                   in
                term_as_mlexpr' g tm
            | uu____6079 ->
                let rec extract_app is_data uu____6124 uu____6125 restArgs =
                  match (uu____6124, uu____6125) with
                  | ((mlhead,mlargs_f),(f,t1)) ->
                      (match (restArgs, t1) with
                       | ([],uu____6215) ->
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
                                | uu____6237 -> false)
                              in
                           let uu____6238 =
                             if evaluation_order_guaranteed
                             then
                               let uu____6263 =
                                 FStar_All.pipe_right
                                   (FStar_List.rev mlargs_f)
                                   (FStar_List.map
                                      FStar_Pervasives_Native.fst)
                                  in
                               ([], uu____6263)
                             else
                               FStar_List.fold_left
                                 (fun uu____6317  ->
                                    fun uu____6318  ->
                                      match (uu____6317, uu____6318) with
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
                                                 ()
                                                in
                                             let uu____6421 =
                                               let uu____6424 =
                                                 FStar_All.pipe_left
                                                   (FStar_Extraction_ML_Syntax.with_ty
                                                      arg.FStar_Extraction_ML_Syntax.mlty)
                                                   (FStar_Extraction_ML_Syntax.MLE_Var
                                                      x)
                                                  in
                                               uu____6424 :: out_args  in
                                             (((x, arg) :: lbs), uu____6421)))
                                 ([], []) mlargs_f
                              in
                           (match uu____6238 with
                            | (lbs,mlargs) ->
                                let app =
                                  let uu____6474 =
                                    FStar_All.pipe_left
                                      (FStar_Extraction_ML_Syntax.with_ty t1)
                                      (FStar_Extraction_ML_Syntax.MLE_App
                                         (mlhead, mlargs))
                                     in
                                  FStar_All.pipe_left
                                    (maybe_eta_data_and_project_record g
                                       is_data t1) uu____6474
                                   in
                                let l_app =
                                  FStar_List.fold_right
                                    (fun uu____6486  ->
                                       fun out  ->
                                         match uu____6486 with
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
                                                     }]) out)) lbs app
                                   in
                                (l_app, f, t1))
                       | ((arg,uu____6507)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                          (formal_t,f',t2)) when
                           (is_type g arg) &&
                             (type_leq g formal_t
                                FStar_Extraction_ML_Syntax.ml_unit_ty)
                           ->
                           let uu____6538 =
                             let uu____6543 =
                               FStar_Extraction_ML_Util.join
                                 arg.FStar_Syntax_Syntax.pos f f'
                                in
                             (uu____6543, t2)  in
                           extract_app is_data
                             (mlhead,
                               ((FStar_Extraction_ML_Syntax.ml_unit,
                                  FStar_Extraction_ML_Syntax.E_PURE) ::
                               mlargs_f)) uu____6538 rest
                       | ((e0,uu____6555)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                          (tExpected,f',t2)) ->
                           let r = e0.FStar_Syntax_Syntax.pos  in
                           let uu____6587 = term_as_mlexpr g e0  in
                           (match uu____6587 with
                            | (e01,f0,tInferred) ->
                                let e02 =
                                  maybe_coerce g e01 tInferred tExpected  in
                                let uu____6604 =
                                  let uu____6609 =
                                    FStar_Extraction_ML_Util.join_l r
                                      [f; f'; f0]
                                     in
                                  (uu____6609, t2)  in
                                extract_app is_data
                                  (mlhead, ((e02, f0) :: mlargs_f))
                                  uu____6604 rest)
                       | uu____6620 ->
                           let uu____6633 =
                             FStar_Extraction_ML_Util.udelta_unfold g t1  in
                           (match uu____6633 with
                            | FStar_Pervasives_Native.Some t2 ->
                                extract_app is_data (mlhead, mlargs_f)
                                  (f, t2) restArgs
                            | FStar_Pervasives_Native.None  ->
                                err_ill_typed_application g top restArgs t1))
                   in
                let extract_app_maybe_projector is_data mlhead uu____6690
                  args1 =
                  match uu____6690 with
                  | (f,t1) ->
                      (match is_data with
                       | FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_projector uu____6722)
                           ->
                           let rec remove_implicits args2 f1 t2 =
                             match (args2, t2) with
                             | ((a0,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____6800))::args3,FStar_Extraction_ML_Syntax.MLTY_Fun
                                (uu____6802,f',t3)) ->
                                 let uu____6839 =
                                   FStar_Extraction_ML_Util.join
                                     a0.FStar_Syntax_Syntax.pos f1 f'
                                    in
                                 remove_implicits args3 uu____6839 t3
                             | uu____6840 -> (args2, f1, t2)  in
                           let uu____6865 = remove_implicits args1 f t1  in
                           (match uu____6865 with
                            | (args2,f1,t2) ->
                                extract_app is_data (mlhead, []) (f1, t2)
                                  args2)
                       | uu____6921 ->
                           extract_app is_data (mlhead, []) (f, t1) args1)
                   in
                let uu____6934 = is_type g t  in
                if uu____6934
                then
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
                else
                  (let head2 = FStar_Syntax_Util.un_uinst head1  in
                   match head2.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_fvar fv when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.fstar_refl_embed_lid)
                         &&
                         (let uu____6951 =
                            let uu____6952 =
                              FStar_Extraction_ML_Syntax.string_of_mlpath
                                g.FStar_Extraction_ML_UEnv.currentModule
                               in
                            uu____6952 = "FStar.Tactics.Builtins"  in
                          Prims.op_Negation uu____6951)
                       ->
                       (match args with
                        | a::b::[] ->
                            term_as_mlexpr g (FStar_Pervasives_Native.fst a)
                        | uu____6993 ->
                            let uu____7002 =
                              FStar_Syntax_Print.args_to_string args  in
                            failwith uu____7002)
                   | FStar_Syntax_Syntax.Tm_name uu____7009 ->
                       let uu____7010 =
                         let uu____7023 =
                           FStar_Extraction_ML_UEnv.lookup_term g head2  in
                         match uu____7023 with
                         | (FStar_Util.Inr (uu____7042,x1,x2,x3),q) ->
                             ((x1, x2, x3), q)
                         | uu____7087 -> failwith "FIXME Ty"  in
                       (match uu____7010 with
                        | ((head_ml,(vars,t1),inst_ok),qual) ->
                            let has_typ_apps =
                              match args with
                              | (a,uu____7137)::uu____7138 -> is_type g a
                              | uu____7157 -> false  in
                            let uu____7166 =
                              match vars with
                              | uu____7195::uu____7196 when
                                  (Prims.op_Negation has_typ_apps) && inst_ok
                                  -> (head_ml, t1, args)
                              | uu____7207 ->
                                  let n1 = FStar_List.length vars  in
                                  if n1 <= (FStar_List.length args)
                                  then
                                    let uu____7235 =
                                      FStar_Util.first_N n1 args  in
                                    (match uu____7235 with
                                     | (prefix1,rest) ->
                                         let prefixAsMLTypes =
                                           FStar_List.map
                                             (fun uu____7324  ->
                                                match uu____7324 with
                                                | (x,uu____7330) ->
                                                    term_as_mlty g x) prefix1
                                            in
                                         let t2 =
                                           instantiate (vars, t1)
                                             prefixAsMLTypes
                                            in
                                         let head3 =
                                           match head_ml.FStar_Extraction_ML_Syntax.expr
                                           with
                                           | FStar_Extraction_ML_Syntax.MLE_Name
                                               uu____7333 ->
                                               let uu___144_7334 = head_ml
                                                  in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (uu___144_7334.FStar_Extraction_ML_Syntax.expr);
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   = t2;
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___144_7334.FStar_Extraction_ML_Syntax.loc)
                                               }
                                           | FStar_Extraction_ML_Syntax.MLE_Var
                                               uu____7335 ->
                                               let uu___144_7336 = head_ml
                                                  in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (uu___144_7336.FStar_Extraction_ML_Syntax.expr);
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   = t2;
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___144_7336.FStar_Extraction_ML_Syntax.loc)
                                               }
                                           | FStar_Extraction_ML_Syntax.MLE_App
                                               (head3,{
                                                        FStar_Extraction_ML_Syntax.expr
                                                          =
                                                          FStar_Extraction_ML_Syntax.MLE_Const
                                                          (FStar_Extraction_ML_Syntax.MLC_Unit
                                                          );
                                                        FStar_Extraction_ML_Syntax.mlty
                                                          = uu____7338;
                                                        FStar_Extraction_ML_Syntax.loc
                                                          = uu____7339;_}::[])
                                               ->
                                               FStar_All.pipe_right
                                                 (FStar_Extraction_ML_Syntax.MLE_App
                                                    ((let uu___145_7345 =
                                                        head3  in
                                                      {
                                                        FStar_Extraction_ML_Syntax.expr
                                                          =
                                                          (uu___145_7345.FStar_Extraction_ML_Syntax.expr);
                                                        FStar_Extraction_ML_Syntax.mlty
                                                          =
                                                          (FStar_Extraction_ML_Syntax.MLTY_Fun
                                                             (FStar_Extraction_ML_Syntax.ml_unit_ty,
                                                               FStar_Extraction_ML_Syntax.E_PURE,
                                                               t2));
                                                        FStar_Extraction_ML_Syntax.loc
                                                          =
                                                          (uu___145_7345.FStar_Extraction_ML_Syntax.loc)
                                                      }),
                                                      [FStar_Extraction_ML_Syntax.ml_unit]))
                                                 (FStar_Extraction_ML_Syntax.with_ty
                                                    t2)
                                           | uu____7346 ->
                                               failwith
                                                 "Impossible: Unexpected head term"
                                            in
                                         (head3, t2, rest))
                                  else err_uninst g head2 (vars, t1) top
                               in
                            (match uu____7166 with
                             | (head_ml1,head_t,args1) ->
                                 (match args1 with
                                  | [] ->
                                      let uu____7407 =
                                        maybe_eta_data_and_project_record g
                                          qual head_t head_ml1
                                         in
                                      (uu____7407,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        head_t)
                                  | uu____7408 ->
                                      extract_app_maybe_projector qual
                                        head_ml1
                                        (FStar_Extraction_ML_Syntax.E_PURE,
                                          head_t) args1)))
                   | FStar_Syntax_Syntax.Tm_fvar uu____7417 ->
                       let uu____7418 =
                         let uu____7431 =
                           FStar_Extraction_ML_UEnv.lookup_term g head2  in
                         match uu____7431 with
                         | (FStar_Util.Inr (uu____7450,x1,x2,x3),q) ->
                             ((x1, x2, x3), q)
                         | uu____7495 -> failwith "FIXME Ty"  in
                       (match uu____7418 with
                        | ((head_ml,(vars,t1),inst_ok),qual) ->
                            let has_typ_apps =
                              match args with
                              | (a,uu____7545)::uu____7546 -> is_type g a
                              | uu____7565 -> false  in
                            let uu____7574 =
                              match vars with
                              | uu____7603::uu____7604 when
                                  (Prims.op_Negation has_typ_apps) && inst_ok
                                  -> (head_ml, t1, args)
                              | uu____7615 ->
                                  let n1 = FStar_List.length vars  in
                                  if n1 <= (FStar_List.length args)
                                  then
                                    let uu____7643 =
                                      FStar_Util.first_N n1 args  in
                                    (match uu____7643 with
                                     | (prefix1,rest) ->
                                         let prefixAsMLTypes =
                                           FStar_List.map
                                             (fun uu____7732  ->
                                                match uu____7732 with
                                                | (x,uu____7738) ->
                                                    term_as_mlty g x) prefix1
                                            in
                                         let t2 =
                                           instantiate (vars, t1)
                                             prefixAsMLTypes
                                            in
                                         let head3 =
                                           match head_ml.FStar_Extraction_ML_Syntax.expr
                                           with
                                           | FStar_Extraction_ML_Syntax.MLE_Name
                                               uu____7741 ->
                                               let uu___144_7742 = head_ml
                                                  in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (uu___144_7742.FStar_Extraction_ML_Syntax.expr);
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   = t2;
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___144_7742.FStar_Extraction_ML_Syntax.loc)
                                               }
                                           | FStar_Extraction_ML_Syntax.MLE_Var
                                               uu____7743 ->
                                               let uu___144_7744 = head_ml
                                                  in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (uu___144_7744.FStar_Extraction_ML_Syntax.expr);
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   = t2;
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___144_7744.FStar_Extraction_ML_Syntax.loc)
                                               }
                                           | FStar_Extraction_ML_Syntax.MLE_App
                                               (head3,{
                                                        FStar_Extraction_ML_Syntax.expr
                                                          =
                                                          FStar_Extraction_ML_Syntax.MLE_Const
                                                          (FStar_Extraction_ML_Syntax.MLC_Unit
                                                          );
                                                        FStar_Extraction_ML_Syntax.mlty
                                                          = uu____7746;
                                                        FStar_Extraction_ML_Syntax.loc
                                                          = uu____7747;_}::[])
                                               ->
                                               FStar_All.pipe_right
                                                 (FStar_Extraction_ML_Syntax.MLE_App
                                                    ((let uu___145_7753 =
                                                        head3  in
                                                      {
                                                        FStar_Extraction_ML_Syntax.expr
                                                          =
                                                          (uu___145_7753.FStar_Extraction_ML_Syntax.expr);
                                                        FStar_Extraction_ML_Syntax.mlty
                                                          =
                                                          (FStar_Extraction_ML_Syntax.MLTY_Fun
                                                             (FStar_Extraction_ML_Syntax.ml_unit_ty,
                                                               FStar_Extraction_ML_Syntax.E_PURE,
                                                               t2));
                                                        FStar_Extraction_ML_Syntax.loc
                                                          =
                                                          (uu___145_7753.FStar_Extraction_ML_Syntax.loc)
                                                      }),
                                                      [FStar_Extraction_ML_Syntax.ml_unit]))
                                                 (FStar_Extraction_ML_Syntax.with_ty
                                                    t2)
                                           | uu____7754 ->
                                               failwith
                                                 "Impossible: Unexpected head term"
                                            in
                                         (head3, t2, rest))
                                  else err_uninst g head2 (vars, t1) top
                               in
                            (match uu____7574 with
                             | (head_ml1,head_t,args1) ->
                                 (match args1 with
                                  | [] ->
                                      let uu____7815 =
                                        maybe_eta_data_and_project_record g
                                          qual head_t head_ml1
                                         in
                                      (uu____7815,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        head_t)
                                  | uu____7816 ->
                                      extract_app_maybe_projector qual
                                        head_ml1
                                        (FStar_Extraction_ML_Syntax.E_PURE,
                                          head_t) args1)))
                   | uu____7825 ->
                       let uu____7826 = term_as_mlexpr g head2  in
                       (match uu____7826 with
                        | (head3,f,t1) ->
                            extract_app_maybe_projector
                              FStar_Pervasives_Native.None head3 (f, t1) args)))
       | FStar_Syntax_Syntax.Tm_ascribed (e0,(tc,uu____7844),f) ->
           let t1 =
             match tc with
             | FStar_Util.Inl t1 -> term_as_mlty g t1
             | FStar_Util.Inr c ->
                 term_as_mlty g (FStar_Syntax_Util.comp_result c)
              in
           let f1 =
             match f with
             | FStar_Pervasives_Native.None  ->
                 failwith "Ascription node with an empty effect label"
             | FStar_Pervasives_Native.Some l -> effect_as_etag g l  in
           let uu____7911 = check_term_as_mlexpr g e0 f1 t1  in
           (match uu____7911 with | (e,t2) -> (e, f1, t2))
       | FStar_Syntax_Syntax.Tm_let ((is_rec,lbs),e') ->
           let top_level = FStar_Syntax_Syntax.is_top_level lbs  in
           let uu____7942 =
             if is_rec
             then FStar_Syntax_Subst.open_let_rec lbs e'
             else
               (let uu____7956 = FStar_Syntax_Syntax.is_top_level lbs  in
                if uu____7956
                then (lbs, e')
                else
                  (let lb = FStar_List.hd lbs  in
                   let x =
                     let uu____7970 =
                       FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                     FStar_Syntax_Syntax.freshen_bv uu____7970  in
                   let lb1 =
                     let uu___146_7972 = lb  in
                     {
                       FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                       FStar_Syntax_Syntax.lbunivs =
                         (uu___146_7972.FStar_Syntax_Syntax.lbunivs);
                       FStar_Syntax_Syntax.lbtyp =
                         (uu___146_7972.FStar_Syntax_Syntax.lbtyp);
                       FStar_Syntax_Syntax.lbeff =
                         (uu___146_7972.FStar_Syntax_Syntax.lbeff);
                       FStar_Syntax_Syntax.lbdef =
                         (uu___146_7972.FStar_Syntax_Syntax.lbdef)
                     }  in
                   let e'1 =
                     FStar_Syntax_Subst.subst
                       [FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x)] e'
                      in
                   ([lb1], e'1)))
              in
           (match uu____7942 with
            | (lbs1,e'1) ->
                let lbs2 =
                  if top_level
                  then
                    FStar_All.pipe_right lbs1
                      (FStar_List.map
                         (fun lb  ->
                            let tcenv =
                              let uu____8004 =
                                FStar_Ident.lid_of_path
                                  (FStar_List.append
                                     (FStar_Pervasives_Native.fst
                                        g.FStar_Extraction_ML_UEnv.currentModule)
                                     [FStar_Pervasives_Native.snd
                                        g.FStar_Extraction_ML_UEnv.currentModule])
                                  FStar_Range.dummyRange
                                 in
                              FStar_TypeChecker_Env.set_current_module
                                g.FStar_Extraction_ML_UEnv.tcenv uu____8004
                               in
                            FStar_Extraction_ML_UEnv.debug g
                              (fun uu____8011  ->
                                 FStar_Options.set_option "debug_level"
                                   (FStar_Options.List
                                      [FStar_Options.String "Norm";
                                      FStar_Options.String "Extraction"]));
                            (let lbdef =
                               let uu____8015 = FStar_Options.ml_ish ()  in
                               if uu____8015
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
                             let uu___147_8019 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___147_8019.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___147_8019.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___147_8019.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___147_8019.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef
                             })))
                  else lbs1  in
                let maybe_generalize uu____8042 =
                  match uu____8042 with
                  | { FStar_Syntax_Syntax.lbname = lbname_;
                      FStar_Syntax_Syntax.lbunivs = uu____8062;
                      FStar_Syntax_Syntax.lbtyp = t1;
                      FStar_Syntax_Syntax.lbeff = lbeff;
                      FStar_Syntax_Syntax.lbdef = e;_} ->
                      let f_e = effect_as_etag g lbeff  in
                      let t2 = FStar_Syntax_Subst.compress t1  in
                      (match t2.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                           let uu____8132 = FStar_List.hd bs  in
                           FStar_All.pipe_right uu____8132 (is_type_binder g)
                           ->
                           let uu____8145 = FStar_Syntax_Subst.open_comp bs c
                              in
                           (match uu____8145 with
                            | (bs1,c1) ->
                                let uu____8170 =
                                  let uu____8177 =
                                    FStar_Util.prefix_until
                                      (fun x  ->
                                         let uu____8213 = is_type_binder g x
                                            in
                                         Prims.op_Negation uu____8213) bs1
                                     in
                                  match uu____8177 with
                                  | FStar_Pervasives_Native.None  ->
                                      (bs1,
                                        (FStar_Syntax_Util.comp_result c1))
                                  | FStar_Pervasives_Native.Some (bs2,b,rest)
                                      ->
                                      let uu____8301 =
                                        FStar_Syntax_Util.arrow (b :: rest)
                                          c1
                                         in
                                      (bs2, uu____8301)
                                   in
                                (match uu____8170 with
                                 | (tbinders,tbody) ->
                                     let n_tbinders =
                                       FStar_List.length tbinders  in
                                     let e1 =
                                       let uu____8346 = normalize_abs e  in
                                       FStar_All.pipe_right uu____8346
                                         FStar_Syntax_Util.unmeta
                                        in
                                     (match e1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Tm_abs
                                          (bs2,body,copt) ->
                                          let uu____8388 =
                                            FStar_Syntax_Subst.open_term bs2
                                              body
                                             in
                                          (match uu____8388 with
                                           | (bs3,body1) ->
                                               if
                                                 n_tbinders <=
                                                   (FStar_List.length bs3)
                                               then
                                                 let uu____8441 =
                                                   FStar_Util.first_N
                                                     n_tbinders bs3
                                                    in
                                                 (match uu____8441 with
                                                  | (targs,rest_args) ->
                                                      let expected_source_ty
                                                        =
                                                        let s =
                                                          FStar_List.map2
                                                            (fun uu____8529 
                                                               ->
                                                               fun uu____8530
                                                                  ->
                                                                 match 
                                                                   (uu____8529,
                                                                    uu____8530)
                                                                 with
                                                                 | ((x,uu____8548),
                                                                    (y,uu____8550))
                                                                    ->
                                                                    let uu____8559
                                                                    =
                                                                    let uu____8566
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    y  in
                                                                    (x,
                                                                    uu____8566)
                                                                     in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____8559)
                                                            tbinders targs
                                                           in
                                                        FStar_Syntax_Subst.subst
                                                          s tbody
                                                         in
                                                      let env =
                                                        FStar_List.fold_left
                                                          (fun env  ->
                                                             fun uu____8577 
                                                               ->
                                                               match uu____8577
                                                               with
                                                               | (a,uu____8583)
                                                                   ->
                                                                   FStar_Extraction_ML_UEnv.extend_ty
                                                                    env a
                                                                    FStar_Pervasives_Native.None)
                                                          g targs
                                                         in
                                                      let expected_t =
                                                        term_as_mlty env
                                                          expected_source_ty
                                                         in
                                                      let polytype =
                                                        let uu____8596 =
                                                          FStar_All.pipe_right
                                                            targs
                                                            (FStar_List.map
                                                               (fun
                                                                  uu____8626 
                                                                  ->
                                                                  match uu____8626
                                                                  with
                                                                  | (x,uu____8636)
                                                                    ->
                                                                    FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                                    x))
                                                           in
                                                        (uu____8596,
                                                          expected_t)
                                                         in
                                                      let add_unit =
                                                        match rest_args with
                                                        | [] ->
                                                            let uu____8648 =
                                                              is_fstar_value
                                                                body1
                                                               in
                                                            Prims.op_Negation
                                                              uu____8648
                                                        | uu____8649 -> false
                                                         in
                                                      let rest_args1 =
                                                        if add_unit
                                                        then unit_binder ::
                                                          rest_args
                                                        else rest_args  in
                                                      let body2 =
                                                        match rest_args1 with
                                                        | [] -> body1
                                                        | uu____8663 ->
                                                            FStar_Syntax_Util.abs
                                                              rest_args1
                                                              body1 copt
                                                         in
                                                      (lbname_, f_e,
                                                        (t2,
                                                          (targs, polytype)),
                                                        add_unit, body2))
                                               else
                                                 failwith
                                                   "Not enough type binders")
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          uu____8749 ->
                                          let env =
                                            FStar_List.fold_left
                                              (fun env  ->
                                                 fun uu____8766  ->
                                                   match uu____8766 with
                                                   | (a,uu____8772) ->
                                                       FStar_Extraction_ML_UEnv.extend_ty
                                                         env a
                                                         FStar_Pervasives_Native.None)
                                              g tbinders
                                             in
                                          let expected_t =
                                            term_as_mlty env tbody  in
                                          let polytype =
                                            let uu____8785 =
                                              FStar_All.pipe_right tbinders
                                                (FStar_List.map
                                                   (fun uu____8809  ->
                                                      match uu____8809 with
                                                      | (x,uu____8819) ->
                                                          FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                            x))
                                               in
                                            (uu____8785, expected_t)  in
                                          let args =
                                            FStar_All.pipe_right tbinders
                                              (FStar_List.map
                                                 (fun uu____8839  ->
                                                    match uu____8839 with
                                                    | (bv,uu____8845) ->
                                                        let uu____8846 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            bv
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____8846
                                                          FStar_Syntax_Syntax.as_arg))
                                             in
                                          let e2 =
                                            FStar_Syntax_Syntax.mk
                                              (FStar_Syntax_Syntax.Tm_app
                                                 (e1, args))
                                              FStar_Pervasives_Native.None
                                              e1.FStar_Syntax_Syntax.pos
                                             in
                                          (lbname_, f_e,
                                            (t2, (tbinders, polytype)),
                                            false, e2)
                                      | FStar_Syntax_Syntax.Tm_fvar
                                          uu____8900 ->
                                          let env =
                                            FStar_List.fold_left
                                              (fun env  ->
                                                 fun uu____8911  ->
                                                   match uu____8911 with
                                                   | (a,uu____8917) ->
                                                       FStar_Extraction_ML_UEnv.extend_ty
                                                         env a
                                                         FStar_Pervasives_Native.None)
                                              g tbinders
                                             in
                                          let expected_t =
                                            term_as_mlty env tbody  in
                                          let polytype =
                                            let uu____8930 =
                                              FStar_All.pipe_right tbinders
                                                (FStar_List.map
                                                   (fun uu____8954  ->
                                                      match uu____8954 with
                                                      | (x,uu____8964) ->
                                                          FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                            x))
                                               in
                                            (uu____8930, expected_t)  in
                                          let args =
                                            FStar_All.pipe_right tbinders
                                              (FStar_List.map
                                                 (fun uu____8984  ->
                                                    match uu____8984 with
                                                    | (bv,uu____8990) ->
                                                        let uu____8991 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            bv
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____8991
                                                          FStar_Syntax_Syntax.as_arg))
                                             in
                                          let e2 =
                                            FStar_Syntax_Syntax.mk
                                              (FStar_Syntax_Syntax.Tm_app
                                                 (e1, args))
                                              FStar_Pervasives_Native.None
                                              e1.FStar_Syntax_Syntax.pos
                                             in
                                          (lbname_, f_e,
                                            (t2, (tbinders, polytype)),
                                            false, e2)
                                      | FStar_Syntax_Syntax.Tm_name
                                          uu____9045 ->
                                          let env =
                                            FStar_List.fold_left
                                              (fun env  ->
                                                 fun uu____9056  ->
                                                   match uu____9056 with
                                                   | (a,uu____9062) ->
                                                       FStar_Extraction_ML_UEnv.extend_ty
                                                         env a
                                                         FStar_Pervasives_Native.None)
                                              g tbinders
                                             in
                                          let expected_t =
                                            term_as_mlty env tbody  in
                                          let polytype =
                                            let uu____9075 =
                                              FStar_All.pipe_right tbinders
                                                (FStar_List.map
                                                   (fun uu____9099  ->
                                                      match uu____9099 with
                                                      | (x,uu____9109) ->
                                                          FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                            x))
                                               in
                                            (uu____9075, expected_t)  in
                                          let args =
                                            FStar_All.pipe_right tbinders
                                              (FStar_List.map
                                                 (fun uu____9129  ->
                                                    match uu____9129 with
                                                    | (bv,uu____9135) ->
                                                        let uu____9136 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            bv
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____9136
                                                          FStar_Syntax_Syntax.as_arg))
                                             in
                                          let e2 =
                                            FStar_Syntax_Syntax.mk
                                              (FStar_Syntax_Syntax.Tm_app
                                                 (e1, args))
                                              FStar_Pervasives_Native.None
                                              e1.FStar_Syntax_Syntax.pos
                                             in
                                          (lbname_, f_e,
                                            (t2, (tbinders, polytype)),
                                            false, e2)
                                      | uu____9190 ->
                                          err_value_restriction e1)))
                       | uu____9209 ->
                           let expected_t = term_as_mlty g t2  in
                           (lbname_, f_e, (t2, ([], ([], expected_t))),
                             false, e))
                   in
                let check_lb env uu____9313 =
                  match uu____9313 with
                  | (nm,(lbname,f,(t1,(targs,polytype)),add_unit,e)) ->
                      let env1 =
                        FStar_List.fold_left
                          (fun env1  ->
                             fun uu____9448  ->
                               match uu____9448 with
                               | (a,uu____9454) ->
                                   FStar_Extraction_ML_UEnv.extend_ty env1 a
                                     FStar_Pervasives_Native.None) env targs
                         in
                      let expected_t =
                        if add_unit
                        then
                          FStar_Extraction_ML_Syntax.MLTY_Fun
                            (FStar_Extraction_ML_Syntax.ml_unit_ty,
                              FStar_Extraction_ML_Syntax.E_PURE,
                              (FStar_Pervasives_Native.snd polytype))
                        else FStar_Pervasives_Native.snd polytype  in
                      let polytype1 =
                        ((FStar_Pervasives_Native.fst polytype), expected_t)
                         in
                      let uu____9462 =
                        check_term_as_mlexpr env1 e f expected_t  in
                      (match uu____9462 with
                       | (e1,uu____9472) ->
                           let f1 = maybe_downgrade_eff env1 f expected_t  in
                           (f1,
                             {
                               FStar_Extraction_ML_Syntax.mllb_name = nm;
                               FStar_Extraction_ML_Syntax.mllb_tysc =
                                 (FStar_Pervasives_Native.Some polytype1);
                               FStar_Extraction_ML_Syntax.mllb_add_unit =
                                 add_unit;
                               FStar_Extraction_ML_Syntax.mllb_def = e1;
                               FStar_Extraction_ML_Syntax.print_typ = true
                             }))
                   in
                let lbs3 =
                  FStar_All.pipe_right lbs2 (FStar_List.map maybe_generalize)
                   in
                let uu____9539 =
                  FStar_List.fold_right
                    (fun lb  ->
                       fun uu____9630  ->
                         match uu____9630 with
                         | (env,lbs4) ->
                             let uu____9755 = lb  in
                             (match uu____9755 with
                              | (lbname,uu____9803,(t1,(uu____9805,polytype)),add_unit,uu____9808)
                                  ->
                                  let uu____9821 =
                                    FStar_Extraction_ML_UEnv.extend_lb env
                                      lbname t1 polytype add_unit true
                                     in
                                  (match uu____9821 with
                                   | (env1,nm) -> (env1, ((nm, lb) :: lbs4)))))
                    lbs3 (g, [])
                   in
                (match uu____9539 with
                 | (env_body,lbs4) ->
                     let env_def = if is_rec then env_body else g  in
                     let lbs5 =
                       FStar_All.pipe_right lbs4
                         (FStar_List.map (check_lb env_def))
                        in
                     let e'_rng = e'1.FStar_Syntax_Syntax.pos  in
                     let uu____10098 = term_as_mlexpr env_body e'1  in
                     (match uu____10098 with
                      | (e'2,f',t') ->
                          let f =
                            let uu____10115 =
                              let uu____10118 =
                                FStar_List.map FStar_Pervasives_Native.fst
                                  lbs5
                                 in
                              f' :: uu____10118  in
                            FStar_Extraction_ML_Util.join_l e'_rng
                              uu____10115
                             in
                          let is_rec1 =
                            if is_rec = true
                            then FStar_Extraction_ML_Syntax.Rec
                            else FStar_Extraction_ML_Syntax.NonRec  in
                          let uu____10127 =
                            let uu____10128 =
                              let uu____10129 =
                                let uu____10130 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    lbs5
                                   in
                                (is_rec1, [], uu____10130)  in
                              mk_MLE_Let top_level uu____10129 e'2  in
                            let uu____10141 =
                              FStar_Extraction_ML_Util.mlloc_of_range
                                t.FStar_Syntax_Syntax.pos
                               in
                            FStar_Extraction_ML_Syntax.with_ty_loc t'
                              uu____10128 uu____10141
                             in
                          (uu____10127, f, t'))))
       | FStar_Syntax_Syntax.Tm_match (scrutinee,pats) ->
           let uu____10180 = term_as_mlexpr g scrutinee  in
           (match uu____10180 with
            | (e,f_e,t_e) ->
                let uu____10196 = check_pats_for_ite pats  in
                (match uu____10196 with
                 | (b,then_e,else_e) ->
                     let no_lift x t1 = x  in
                     if b
                     then
                       (match (then_e, else_e) with
                        | (FStar_Pervasives_Native.Some
                           then_e1,FStar_Pervasives_Native.Some else_e1) ->
                            let uu____10253 = term_as_mlexpr g then_e1  in
                            (match uu____10253 with
                             | (then_mle,f_then,t_then) ->
                                 let uu____10269 = term_as_mlexpr g else_e1
                                    in
                                 (match uu____10269 with
                                  | (else_mle,f_else,t_else) ->
                                      let uu____10285 =
                                        let uu____10294 =
                                          type_leq g t_then t_else  in
                                        if uu____10294
                                        then (t_else, no_lift)
                                        else
                                          (let uu____10308 =
                                             type_leq g t_else t_then  in
                                           if uu____10308
                                           then (t_then, no_lift)
                                           else
                                             (FStar_Extraction_ML_Syntax.MLTY_Top,
                                               FStar_Extraction_ML_Syntax.apply_obj_repr))
                                         in
                                      (match uu____10285 with
                                       | (t_branch,maybe_lift1) ->
                                           let uu____10342 =
                                             let uu____10343 =
                                               let uu____10344 =
                                                 let uu____10353 =
                                                   maybe_lift1 then_mle
                                                     t_then
                                                    in
                                                 let uu____10354 =
                                                   let uu____10357 =
                                                     maybe_lift1 else_mle
                                                       t_else
                                                      in
                                                   FStar_Pervasives_Native.Some
                                                     uu____10357
                                                    in
                                                 (e, uu____10353,
                                                   uu____10354)
                                                  in
                                               FStar_Extraction_ML_Syntax.MLE_If
                                                 uu____10344
                                                in
                                             FStar_All.pipe_left
                                               (FStar_Extraction_ML_Syntax.with_ty
                                                  t_branch) uu____10343
                                              in
                                           let uu____10360 =
                                             FStar_Extraction_ML_Util.join
                                               then_e1.FStar_Syntax_Syntax.pos
                                               f_then f_else
                                              in
                                           (uu____10342, uu____10360,
                                             t_branch))))
                        | uu____10361 ->
                            failwith
                              "ITE pats matched but then and else expressions not found?")
                     else
                       (let uu____10377 =
                          FStar_All.pipe_right pats
                            (FStar_Util.fold_map
                               (fun compat  ->
                                  fun br  ->
                                    let uu____10486 =
                                      FStar_Syntax_Subst.open_branch br  in
                                    match uu____10486 with
                                    | (pat,when_opt,branch1) ->
                                        let uu____10530 =
                                          extract_pat g pat t_e  in
                                        (match uu____10530 with
                                         | (env,p,pat_t_compat) ->
                                             let uu____10588 =
                                               match when_opt with
                                               | FStar_Pervasives_Native.None
                                                    ->
                                                   (FStar_Pervasives_Native.None,
                                                     FStar_Extraction_ML_Syntax.E_PURE)
                                               | FStar_Pervasives_Native.Some
                                                   w ->
                                                   let uu____10610 =
                                                     term_as_mlexpr env w  in
                                                   (match uu____10610 with
                                                    | (w1,f_w,t_w) ->
                                                        let w2 =
                                                          maybe_coerce env w1
                                                            t_w
                                                            FStar_Extraction_ML_Syntax.ml_bool_ty
                                                           in
                                                        ((FStar_Pervasives_Native.Some
                                                            w2), f_w))
                                                in
                                             (match uu____10588 with
                                              | (when_opt1,f_when) ->
                                                  let uu____10659 =
                                                    term_as_mlexpr env
                                                      branch1
                                                     in
                                                  (match uu____10659 with
                                                   | (mlbranch,f_branch,t_branch)
                                                       ->
                                                       let uu____10693 =
                                                         FStar_All.pipe_right
                                                           p
                                                           (FStar_List.map
                                                              (fun
                                                                 uu____10770 
                                                                 ->
                                                                 match uu____10770
                                                                 with
                                                                 | (p1,wopt)
                                                                    ->
                                                                    let when_clause
                                                                    =
                                                                    FStar_Extraction_ML_Util.conjoin_opt
                                                                    wopt
                                                                    when_opt1
                                                                     in
                                                                    (p1,
                                                                    (when_clause,
                                                                    f_when),
                                                                    (mlbranch,
                                                                    f_branch,
                                                                    t_branch))))
                                                          in
                                                       ((compat &&
                                                           pat_t_compat),
                                                         uu____10693)))))
                               true)
                           in
                        match uu____10377 with
                        | (pat_t_compat,mlbranches) ->
                            let mlbranches1 = FStar_List.flatten mlbranches
                               in
                            let e1 =
                              if pat_t_compat
                              then e
                              else
                                (FStar_Extraction_ML_UEnv.debug g
                                   (fun uu____10935  ->
                                      let uu____10936 =
                                        FStar_Extraction_ML_Code.string_of_mlexpr
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          e
                                         in
                                      let uu____10937 =
                                        FStar_Extraction_ML_Code.string_of_mlty
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          t_e
                                         in
                                      FStar_Util.print2
                                        "Coercing scrutinee %s from type %s because pattern type is incompatible\n"
                                        uu____10936 uu____10937);
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty t_e)
                                   (FStar_Extraction_ML_Syntax.MLE_Coerce
                                      (e, t_e,
                                        FStar_Extraction_ML_Syntax.MLTY_Top)))
                               in
                            (match mlbranches1 with
                             | [] ->
                                 let uu____10962 =
                                   let uu____10971 =
                                     let uu____10988 =
                                       FStar_Syntax_Syntax.lid_as_fv
                                         FStar_Parser_Const.failwith_lid
                                         FStar_Syntax_Syntax.Delta_constant
                                         FStar_Pervasives_Native.None
                                        in
                                     FStar_Extraction_ML_UEnv.lookup_fv g
                                       uu____10988
                                      in
                                   FStar_All.pipe_left FStar_Util.right
                                     uu____10971
                                    in
                                 (match uu____10962 with
                                  | (uu____11031,fw,uu____11033,uu____11034)
                                      ->
                                      let uu____11035 =
                                        let uu____11036 =
                                          let uu____11037 =
                                            let uu____11044 =
                                              let uu____11047 =
                                                FStar_All.pipe_left
                                                  (FStar_Extraction_ML_Syntax.with_ty
                                                     FStar_Extraction_ML_Syntax.ml_string_ty)
                                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                                     (FStar_Extraction_ML_Syntax.MLC_String
                                                        "unreachable"))
                                                 in
                                              [uu____11047]  in
                                            (fw, uu____11044)  in
                                          FStar_Extraction_ML_Syntax.MLE_App
                                            uu____11037
                                           in
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             FStar_Extraction_ML_Syntax.ml_unit_ty)
                                          uu____11036
                                         in
                                      (uu____11035,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        FStar_Extraction_ML_Syntax.ml_unit_ty))
                             | (uu____11050,uu____11051,(uu____11052,f_first,t_first))::rest
                                 ->
                                 let uu____11112 =
                                   FStar_List.fold_left
                                     (fun uu____11154  ->
                                        fun uu____11155  ->
                                          match (uu____11154, uu____11155)
                                          with
                                          | ((topt,f),(uu____11212,uu____11213,
                                                       (uu____11214,f_branch,t_branch)))
                                              ->
                                              let f1 =
                                                FStar_Extraction_ML_Util.join
                                                  top.FStar_Syntax_Syntax.pos
                                                  f f_branch
                                                 in
                                              let topt1 =
                                                match topt with
                                                | FStar_Pervasives_Native.None
                                                     ->
                                                    FStar_Pervasives_Native.None
                                                | FStar_Pervasives_Native.Some
                                                    t1 ->
                                                    let uu____11270 =
                                                      type_leq g t1 t_branch
                                                       in
                                                    if uu____11270
                                                    then
                                                      FStar_Pervasives_Native.Some
                                                        t_branch
                                                    else
                                                      (let uu____11274 =
                                                         type_leq g t_branch
                                                           t1
                                                          in
                                                       if uu____11274
                                                       then
                                                         FStar_Pervasives_Native.Some
                                                           t1
                                                       else
                                                         FStar_Pervasives_Native.None)
                                                 in
                                              (topt1, f1))
                                     ((FStar_Pervasives_Native.Some t_first),
                                       f_first) rest
                                    in
                                 (match uu____11112 with
                                  | (topt,f_match) ->
                                      let mlbranches2 =
                                        FStar_All.pipe_right mlbranches1
                                          (FStar_List.map
                                             (fun uu____11369  ->
                                                match uu____11369 with
                                                | (p,(wopt,uu____11398),
                                                   (b1,uu____11400,t1)) ->
                                                    let b2 =
                                                      match topt with
                                                      | FStar_Pervasives_Native.None
                                                           ->
                                                          FStar_Extraction_ML_Syntax.apply_obj_repr
                                                            b1 t1
                                                      | FStar_Pervasives_Native.Some
                                                          uu____11419 -> b1
                                                       in
                                                    (p, wopt, b2)))
                                         in
                                      let t_match =
                                        match topt with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Extraction_ML_Syntax.MLTY_Top
                                        | FStar_Pervasives_Native.Some t1 ->
                                            t1
                                         in
                                      let uu____11424 =
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             t_match)
                                          (FStar_Extraction_ML_Syntax.MLE_Match
                                             (e1, mlbranches2))
                                         in
                                      (uu____11424, f_match, t_match)))))))

let ind_discriminator_body :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlmodule1
  =
  fun env  ->
    fun discName  ->
      fun constrName  ->
        let uu____11447 =
          let uu____11452 =
            FStar_TypeChecker_Env.lookup_lid
              env.FStar_Extraction_ML_UEnv.tcenv discName
             in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____11452  in
        match uu____11447 with
        | (uu____11477,fstar_disc_type) ->
            let wildcards =
              let uu____11490 =
                let uu____11491 = FStar_Syntax_Subst.compress fstar_disc_type
                   in
                uu____11491.FStar_Syntax_Syntax.n  in
              match uu____11490 with
              | FStar_Syntax_Syntax.Tm_arrow (binders,uu____11505) ->
                  let uu____11522 =
                    FStar_All.pipe_right binders
                      (FStar_List.filter
                         (fun uu___141_11554  ->
                            match uu___141_11554 with
                            | (uu____11561,FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____11562)) ->
                                true
                            | uu____11565 -> false))
                     in
                  FStar_All.pipe_right uu____11522
                    (FStar_List.map
                       (fun uu____11606  ->
                          let uu____11613 = fresh "_"  in
                          (uu____11613, FStar_Extraction_ML_Syntax.MLTY_Top)))
              | uu____11622 -> failwith "Discriminator must be a function"
               in
            let mlid = fresh "_discr_"  in
            let targ = FStar_Extraction_ML_Syntax.MLTY_Top  in
            let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top  in
            let discrBody =
              let uu____11641 =
                let uu____11642 =
                  let uu____11653 =
                    let uu____11654 =
                      let uu____11655 =
                        let uu____11670 =
                          let uu____11671 =
                            let uu____11672 =
                              let uu____11673 =
                                FStar_Extraction_ML_Syntax.idsym mlid  in
                              ([], uu____11673)  in
                            FStar_Extraction_ML_Syntax.MLE_Name uu____11672
                             in
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty targ)
                            uu____11671
                           in
                        let uu____11676 =
                          let uu____11687 =
                            let uu____11696 =
                              let uu____11697 =
                                let uu____11704 =
                                  FStar_Extraction_ML_Syntax.mlpath_of_lident
                                    constrName
                                   in
                                (uu____11704,
                                  [FStar_Extraction_ML_Syntax.MLP_Wild])
                                 in
                              FStar_Extraction_ML_Syntax.MLP_CTor uu____11697
                               in
                            let uu____11707 =
                              FStar_All.pipe_left
                                (FStar_Extraction_ML_Syntax.with_ty
                                   FStar_Extraction_ML_Syntax.ml_bool_ty)
                                (FStar_Extraction_ML_Syntax.MLE_Const
                                   (FStar_Extraction_ML_Syntax.MLC_Bool true))
                               in
                            (uu____11696, FStar_Pervasives_Native.None,
                              uu____11707)
                             in
                          let uu____11710 =
                            let uu____11721 =
                              let uu____11730 =
                                FStar_All.pipe_left
                                  (FStar_Extraction_ML_Syntax.with_ty
                                     FStar_Extraction_ML_Syntax.ml_bool_ty)
                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                     (FStar_Extraction_ML_Syntax.MLC_Bool
                                        false))
                                 in
                              (FStar_Extraction_ML_Syntax.MLP_Wild,
                                FStar_Pervasives_Native.None, uu____11730)
                               in
                            [uu____11721]  in
                          uu____11687 :: uu____11710  in
                        (uu____11670, uu____11676)  in
                      FStar_Extraction_ML_Syntax.MLE_Match uu____11655  in
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.ml_bool_ty) uu____11654
                     in
                  ((FStar_List.append wildcards [(mlid, targ)]), uu____11653)
                   in
                FStar_Extraction_ML_Syntax.MLE_Fun uu____11642  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty disc_ty) uu____11641
               in
            let uu____11805 =
              let uu____11806 =
                let uu____11809 =
                  let uu____11810 =
                    FStar_Extraction_ML_UEnv.convIdent
                      discName.FStar_Ident.ident
                     in
                  {
                    FStar_Extraction_ML_Syntax.mllb_name = uu____11810;
                    FStar_Extraction_ML_Syntax.mllb_tysc =
                      FStar_Pervasives_Native.None;
                    FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                    FStar_Extraction_ML_Syntax.mllb_def = discrBody;
                    FStar_Extraction_ML_Syntax.print_typ = false
                  }  in
                [uu____11809]  in
              (FStar_Extraction_ML_Syntax.NonRec, [], uu____11806)  in
            FStar_Extraction_ML_Syntax.MLM_Let uu____11805
  