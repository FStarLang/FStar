open Prims
<<<<<<< HEAD
exception Un_extractable 
let uu___is_Un_extractable : Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Un_extractable  -> true | uu____5 -> false
  
let type_leq :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlty -> Prims.bool
  =
=======
exception Un_extractable
let (uu___is_Un_extractable :Prims.exn -> Prims.bool)=
  fun projectee  ->
    match projectee with | Un_extractable  -> true | uu____5 -> false
let (type_leq
  :FStar_Extraction_ML_UEnv.env ->
     FStar_Extraction_ML_Syntax.mlty ->
       FStar_Extraction_ML_Syntax.mlty -> Prims.bool)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun g  ->
    fun t1  ->
      fun t2  ->
        FStar_Extraction_ML_Util.type_leq
          (FStar_Extraction_ML_Util.udelta_unfold g) t1 t2
<<<<<<< HEAD
  
let type_leq_c :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option ->
      FStar_Extraction_ML_Syntax.mlty ->
        FStar_Extraction_ML_Syntax.mlty ->
          (Prims.bool,FStar_Extraction_ML_Syntax.mlexpr
                        FStar_Pervasives_Native.option)
            FStar_Pervasives_Native.tuple2
  =
=======
let (type_leq_c
  :FStar_Extraction_ML_UEnv.env ->
     FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option ->
       FStar_Extraction_ML_Syntax.mlty ->
         FStar_Extraction_ML_Syntax.mlty ->
           (Prims.bool,FStar_Extraction_ML_Syntax.mlexpr
                         FStar_Pervasives_Native.option)
             FStar_Pervasives_Native.tuple2)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun g  ->
    fun t1  ->
      fun t2  ->
        FStar_Extraction_ML_Util.type_leq_c
          (FStar_Extraction_ML_Util.udelta_unfold g) t1 t2
<<<<<<< HEAD
  
let erasableType :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.mlty -> Prims.bool
  =
=======
let (erasableType
  :FStar_Extraction_ML_UEnv.env ->
     FStar_Extraction_ML_Syntax.mlty -> Prims.bool)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun g  ->
    fun t  ->
      FStar_Extraction_ML_Util.erasableType
        (FStar_Extraction_ML_Util.udelta_unfold g) t
<<<<<<< HEAD
  
let eraseTypeDeep :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty
  =
=======
let (eraseTypeDeep
  :FStar_Extraction_ML_UEnv.env ->
     FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun g  ->
    fun t  ->
      FStar_Extraction_ML_Util.eraseTypeDeep
        (FStar_Extraction_ML_Util.udelta_unfold g) t
<<<<<<< HEAD
  
=======
>>>>>>> taramana_pointers_with_codes_modifies
let record_fields :
  'Auu____65 .
    FStar_Ident.ident Prims.list ->
      'Auu____65 Prims.list ->
        (Prims.string,'Auu____65) FStar_Pervasives_Native.tuple2 Prims.list=
  fun fs  ->
    fun vs  ->
      FStar_List.map2 (fun f  -> fun e  -> ((f.FStar_Ident.idText), e)) fs vs
<<<<<<< HEAD
  
let fail : 'Auu____102 . FStar_Range.range -> Prims.string -> 'Auu____102 =
=======
let fail : 'Auu____102 . FStar_Range.range -> Prims.string -> 'Auu____102=
>>>>>>> taramana_pointers_with_codes_modifies
  fun r  ->
    fun msg  ->
      (let uu____112 =
         let uu____113 = FStar_Range.string_of_range r  in
         FStar_Util.format2 "%s: %s\n" uu____113 msg  in
       FStar_All.pipe_left FStar_Util.print_string uu____112);
      failwith msg
<<<<<<< HEAD
  
=======
>>>>>>> taramana_pointers_with_codes_modifies
let err_uninst :
  'Auu____126 'Auu____127 .
    FStar_Extraction_ML_UEnv.env ->
      FStar_Syntax_Syntax.term ->
        ((Prims.string,'Auu____127) FStar_Pervasives_Native.tuple2 Prims.list,
          FStar_Extraction_ML_Syntax.mlty) FStar_Pervasives_Native.tuple2 ->
          FStar_Syntax_Syntax.term -> 'Auu____126=
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
<<<<<<< HEAD
  
=======
>>>>>>> taramana_pointers_with_codes_modifies
let err_ill_typed_application :
  'Auu____212 'Auu____213 .
    FStar_Extraction_ML_UEnv.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term,'Auu____213) FStar_Pervasives_Native.tuple2
          Prims.list -> FStar_Extraction_ML_Syntax.mlty -> 'Auu____212=
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
<<<<<<< HEAD
  
=======
>>>>>>> taramana_pointers_with_codes_modifies
let err_value_restriction :
  'Auu____277 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> 'Auu____277=
  fun t  ->
    let uu____286 =
      let uu____287 = FStar_Syntax_Print.tag_of_term t  in
      let uu____288 = FStar_Syntax_Print.term_to_string t  in
      FStar_Util.format2
        "Refusing to generalize because of the value restriction: (%s) %s"
        uu____287 uu____288
       in
    fail t.FStar_Syntax_Syntax.pos uu____286
<<<<<<< HEAD
  
=======
>>>>>>> taramana_pointers_with_codes_modifies
let err_unexpected_eff :
  'Auu____297 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Extraction_ML_Syntax.e_tag ->
        FStar_Extraction_ML_Syntax.e_tag -> 'Auu____297=
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
<<<<<<< HEAD
  
let effect_as_etag :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Ident.lident -> FStar_Extraction_ML_Syntax.e_tag
  =
  let cache = FStar_Util.smap_create (Prims.parse_int "20")  in
=======
let (effect_as_etag
  :FStar_Extraction_ML_UEnv.env ->
     FStar_Ident.lident -> FStar_Extraction_ML_Syntax.e_tag)=
  let cache = FStar_Util.smap_create (Prims.parse_int "20") in
>>>>>>> taramana_pointers_with_codes_modifies
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
<<<<<<< HEAD
  
let rec is_arity :
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool =
=======
let rec (is_arity
  :FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool)=
>>>>>>> taramana_pointers_with_codes_modifies
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
<<<<<<< HEAD
  
let rec is_type_aux :
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool =
=======
let rec (is_type_aux
  :FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool)=
>>>>>>> taramana_pointers_with_codes_modifies
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
<<<<<<< HEAD
  
let is_type :
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool =
=======
let (is_type
  :FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool)=
>>>>>>> taramana_pointers_with_codes_modifies
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
<<<<<<< HEAD
  
=======
>>>>>>> taramana_pointers_with_codes_modifies
let is_type_binder :
  'Auu____1132 .
    FStar_Extraction_ML_UEnv.env ->
      (FStar_Syntax_Syntax.bv,'Auu____1132) FStar_Pervasives_Native.tuple2 ->
        Prims.bool=
  fun env  ->
    fun x  ->
      is_arity env (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
<<<<<<< HEAD
  
let is_constructor : FStar_Syntax_Syntax.term -> Prims.bool =
=======
let (is_constructor :FStar_Syntax_Syntax.term -> Prims.bool)=
>>>>>>> taramana_pointers_with_codes_modifies
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
<<<<<<< HEAD
  
let rec is_fstar_value : FStar_Syntax_Syntax.term -> Prims.bool =
=======
let rec (is_fstar_value :FStar_Syntax_Syntax.term -> Prims.bool)=
>>>>>>> taramana_pointers_with_codes_modifies
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
<<<<<<< HEAD
  
let rec is_ml_value : FStar_Extraction_ML_Syntax.mlexpr -> Prims.bool =
=======
let rec (is_ml_value :FStar_Extraction_ML_Syntax.mlexpr -> Prims.bool)=
>>>>>>> taramana_pointers_with_codes_modifies
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
<<<<<<< HEAD
    | FStar_Extraction_ML_Syntax.MLE_TApp (h,uu____1353) -> is_ml_value h
    | uu____1358 -> false
  
let fresh :
  Prims.string -> (Prims.string,Prims.int) FStar_Pervasives_Native.tuple2 =
  let c = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun x  ->
    FStar_Util.incr c;
    (let uu____1392 =
       let uu____1393 =
         let uu____1394 = FStar_ST.op_Bang c  in
         FStar_Util.string_of_int uu____1394  in
       Prims.strcat x uu____1393  in
     let uu____1419 = FStar_ST.op_Bang c  in (uu____1392, uu____1419))
  
let normalize_abs : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
=======
    | uu____1352 -> false
let (fresh
  :Prims.string -> (Prims.string,Prims.int) FStar_Pervasives_Native.tuple2)=
  let c = FStar_Util.mk_ref (Prims.parse_int "0") in
  fun x  ->
    FStar_Util.incr c;
    (let uu____1386 =
       let uu____1387 =
         let uu____1388 = FStar_ST.op_Bang c in
         FStar_Util.string_of_int uu____1388 in
       Prims.strcat x uu____1387 in
     let uu____1413 = FStar_ST.op_Bang c in (uu____1386, uu____1413))
let (normalize_abs :FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun t0  ->
    let rec aux bs t copt =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_abs (bs',body,copt1) ->
          aux (FStar_List.append bs bs') body copt1
      | uu____1502 ->
          let e' = FStar_Syntax_Util.unascribe t1  in
          let uu____1504 = FStar_Syntax_Util.is_fun e'  in
          if uu____1504
          then aux bs e' copt
          else FStar_Syntax_Util.abs bs e' copt
       in
    aux [] t0 FStar_Pervasives_Native.None
<<<<<<< HEAD
  
let unit_binder : FStar_Syntax_Syntax.binder =
  let uu____1510 =
    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
      FStar_Syntax_Syntax.t_unit
     in
  FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____1510 
let check_pats_for_ite :
  (FStar_Syntax_Syntax.pat,FStar_Syntax_Syntax.term
                             FStar_Pervasives_Native.option,FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.tuple3 Prims.list ->
    (Prims.bool,FStar_Syntax_Syntax.term FStar_Pervasives_Native.option,
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3
  =
=======
let (unit_binder :FStar_Syntax_Syntax.binder)=
  let uu____1504 =
    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
      FStar_Syntax_Syntax.t_unit in
  FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____1504
let (check_pats_for_ite
  :(FStar_Syntax_Syntax.pat,FStar_Syntax_Syntax.term
                              FStar_Pervasives_Native.option,FStar_Syntax_Syntax.term)
     FStar_Pervasives_Native.tuple3 Prims.list ->
     (Prims.bool,FStar_Syntax_Syntax.term FStar_Pervasives_Native.option,
       FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
       FStar_Pervasives_Native.tuple3)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun l  ->
    let def =
      (false, FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)  in
    if (FStar_List.length l) <> (Prims.parse_int "2")
    then def
    else
      (let uu____1589 = FStar_List.hd l  in
       match uu____1589 with
       | (p1,w1,e1) ->
           let uu____1623 =
             let uu____1632 = FStar_List.tl l  in FStar_List.hd uu____1632
              in
           (match uu____1623 with
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
<<<<<<< HEAD
                 | uu____1706 -> def)))
  
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
=======
                 | uu____1700 -> def)))
let (instantiate
  :FStar_Extraction_ML_Syntax.mltyscheme ->
     FStar_Extraction_ML_Syntax.mlty Prims.list ->
       FStar_Extraction_ML_Syntax.mlty)=
  fun s  -> fun args  -> FStar_Extraction_ML_Util.subst s args
let (erasable
  :FStar_Extraction_ML_UEnv.env ->
     FStar_Extraction_ML_Syntax.e_tag ->
       FStar_Extraction_ML_Syntax.mlty -> Prims.bool)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun g  ->
    fun f  ->
      fun t  ->
        (f = FStar_Extraction_ML_Syntax.E_GHOST) ||
          ((f = FStar_Extraction_ML_Syntax.E_PURE) && (erasableType g t))
<<<<<<< HEAD
  
let erase :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.mlexpr ->
      FStar_Extraction_ML_Syntax.mlty ->
        FStar_Extraction_ML_Syntax.e_tag ->
          (FStar_Extraction_ML_Syntax.mlexpr,FStar_Extraction_ML_Syntax.e_tag,
            FStar_Extraction_ML_Syntax.mlty) FStar_Pervasives_Native.tuple3
  =
=======
let (erase
  :FStar_Extraction_ML_UEnv.env ->
     FStar_Extraction_ML_Syntax.mlexpr ->
       FStar_Extraction_ML_Syntax.mlty ->
         FStar_Extraction_ML_Syntax.e_tag ->
           (FStar_Extraction_ML_Syntax.mlexpr,FStar_Extraction_ML_Syntax.e_tag,
             FStar_Extraction_ML_Syntax.mlty) FStar_Pervasives_Native.tuple3)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun g  ->
    fun e  ->
      fun ty  ->
        fun f  ->
          let e1 =
            let uu____1772 = erasable g f ty  in
            if uu____1772
            then
              let uu____1773 =
                type_leq g ty FStar_Extraction_ML_Syntax.ml_unit_ty  in
              (if uu____1773
               then FStar_Extraction_ML_Syntax.ml_unit
               else
                 FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty)
                   (FStar_Extraction_ML_Syntax.MLE_Coerce
                      (FStar_Extraction_ML_Syntax.ml_unit,
                        FStar_Extraction_ML_Syntax.ml_unit_ty, ty)))
            else e  in
          (e1, f, ty)
<<<<<<< HEAD
  
let eta_expand :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr
  =
=======
let (eta_expand
  :FStar_Extraction_ML_Syntax.mlty ->
     FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun t  ->
    fun e  ->
      let uu____1784 = FStar_Extraction_ML_Util.doms_and_cod t  in
      match uu____1784 with
      | (ts,r) ->
          if ts = []
          then e
          else
            (let vs = FStar_List.map (fun uu____1812  -> fresh "a") ts  in
             let vs_ts = FStar_List.zip vs ts  in
             let vs_es =
               let uu____1831 = FStar_List.zip vs ts  in
               FStar_List.map
                 (fun uu____1849  ->
                    match uu____1849 with
                    | (v1,t1) ->
                        FStar_Extraction_ML_Syntax.with_ty t1
                          (FStar_Extraction_ML_Syntax.MLE_Var v1)) uu____1831
                in
             let body =
               FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty r)
                 (FStar_Extraction_ML_Syntax.MLE_App (e, vs_es))
                in
             FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t)
               (FStar_Extraction_ML_Syntax.MLE_Fun (vs_ts, body)))
<<<<<<< HEAD
  
let maybe_eta_expand :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr
  =
=======
let (maybe_eta_expand
  :FStar_Extraction_ML_Syntax.mlty ->
     FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun expect  ->
    fun e  ->
      let uu____1877 =
        (FStar_Options.ml_no_eta_expand_coertions ()) ||
<<<<<<< HEAD
          (let uu____1879 = FStar_Options.codegen ()  in
           uu____1879 = (FStar_Pervasives_Native.Some "Kremlin"))
         in
      if uu____1877 then e else eta_expand expect e
  
let maybe_coerce :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.mlexpr ->
      FStar_Extraction_ML_Syntax.mlty ->
        FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlexpr
  =
=======
          (let uu____1873 = FStar_Options.codegen () in
           uu____1873 = (FStar_Pervasives_Native.Some "Kremlin")) in
      if uu____1871 then e else eta_expand expect e
let (maybe_coerce
  :FStar_Extraction_ML_UEnv.env ->
     FStar_Extraction_ML_Syntax.mlexpr ->
       FStar_Extraction_ML_Syntax.mlty ->
         FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlexpr)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun g  ->
    fun e  ->
      fun ty  ->
        fun expect  ->
          let ty1 = eraseTypeDeep g ty  in
          let uu____1902 =
            type_leq_c g (FStar_Pervasives_Native.Some e) ty1 expect  in
          match uu____1902 with
          | (true ,FStar_Pervasives_Native.Some e') -> e'
          | uu____1912 ->
              (FStar_Extraction_ML_UEnv.debug g
                 (fun uu____1924  ->
                    let uu____1925 =
                      FStar_Extraction_ML_Code.string_of_mlexpr
                        g.FStar_Extraction_ML_UEnv.currentModule e
                       in
                    let uu____1926 =
                      FStar_Extraction_ML_Code.string_of_mlty
                        g.FStar_Extraction_ML_UEnv.currentModule ty1
                       in
                    let uu____1927 =
                      FStar_Extraction_ML_Code.string_of_mlty
                        g.FStar_Extraction_ML_UEnv.currentModule expect
                       in
                    FStar_Util.print3
                      "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n"
                      uu____1925 uu____1926 uu____1927);
               (let uu____1928 =
                  FStar_All.pipe_left
                    (FStar_Extraction_ML_Syntax.with_ty expect)
<<<<<<< HEAD
                    (FStar_Extraction_ML_Syntax.MLE_Coerce (e, ty1, expect))
                   in
                maybe_eta_expand expect uu____1928))
  
let bv_as_mlty :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlty
  =
  fun g  ->
    fun bv  ->
      let uu____1937 = FStar_Extraction_ML_UEnv.lookup_bv g bv  in
      match uu____1937 with
      | FStar_Util.Inl (uu____1938,t) -> t
      | uu____1952 -> FStar_Extraction_ML_Syntax.MLTY_Top
  
let rec term_as_mlty :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlty
  =
=======
                    (FStar_Extraction_ML_Syntax.MLE_Coerce (e, ty1, expect)) in
                maybe_eta_expand expect uu____1922))
let (bv_as_mlty
  :FStar_Extraction_ML_UEnv.env ->
     FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlty)=
  fun g  ->
    fun bv  ->
      let uu____1931 = FStar_Extraction_ML_UEnv.lookup_bv g bv in
      match uu____1931 with
      | FStar_Util.Inl (uu____1932,t) -> t
      | uu____1946 -> FStar_Extraction_ML_Syntax.MLTY_Top
let rec (term_as_mlty
  :FStar_Extraction_ML_UEnv.env ->
     FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlty)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun g  ->
    fun t0  ->
      let rec is_top_ty t =
        match t with
        | FStar_Extraction_ML_Syntax.MLTY_Top  -> true
        | FStar_Extraction_ML_Syntax.MLTY_Named uu____1995 ->
            let uu____2002 = FStar_Extraction_ML_Util.udelta_unfold g t  in
            (match uu____2002 with
             | FStar_Pervasives_Native.None  -> false
             | FStar_Pervasives_Native.Some t1 -> is_top_ty t1)
        | uu____2006 -> false  in
      let t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.Iota;
          FStar_TypeChecker_Normalize.Zeta;
          FStar_TypeChecker_Normalize.Inlining;
          FStar_TypeChecker_Normalize.EraseUniverses;
          FStar_TypeChecker_Normalize.AllowUnboundUniverses]
          g.FStar_Extraction_ML_UEnv.tcenv t0
         in
      let mlt = term_as_mlty' g t  in
      let uu____2009 = is_top_ty mlt  in
      if uu____2009
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
            g.FStar_Extraction_ML_UEnv.tcenv t0
           in
        term_as_mlty' g t1
      else mlt
<<<<<<< HEAD

and term_as_mlty' :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlty
  =
=======
and (term_as_mlty'
  :FStar_Extraction_ML_UEnv.env ->
     FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlty)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_bvar uu____2015 ->
          let uu____2016 =
            let uu____2017 = FStar_Syntax_Print.term_to_string t1  in
            FStar_Util.format1 "Impossible: Unexpected term %s" uu____2017
             in
          failwith uu____2016
      | FStar_Syntax_Syntax.Tm_delayed uu____2018 ->
          let uu____2043 =
            let uu____2044 = FStar_Syntax_Print.term_to_string t1  in
            FStar_Util.format1 "Impossible: Unexpected term %s" uu____2044
             in
          failwith uu____2043
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____2045 =
            let uu____2046 = FStar_Syntax_Print.term_to_string t1  in
            FStar_Util.format1 "Impossible: Unexpected term %s" uu____2046
             in
          failwith uu____2045
      | FStar_Syntax_Syntax.Tm_constant uu____2047 ->
          FStar_Extraction_ML_UEnv.unknownType
      | FStar_Syntax_Syntax.Tm_uvar uu____2048 ->
          FStar_Extraction_ML_UEnv.unknownType
      | FStar_Syntax_Syntax.Tm_meta (t2,uu____2066) -> term_as_mlty' env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____2071;
             FStar_Syntax_Syntax.index = uu____2072;
             FStar_Syntax_Syntax.sort = t2;_},uu____2074)
          -> term_as_mlty' env t2
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____2082) -> term_as_mlty' env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____2088,uu____2089) ->
          term_as_mlty' env t2
      | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
      | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv []
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____2156 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____2156 with
           | (bs1,c1) ->
               let uu____2163 = binders_as_ml_binders env bs1  in
               (match uu____2163 with
                | (mlbs,env1) ->
                    let t_ret =
                      let eff =
                        FStar_TypeChecker_Env.norm_eff_name
                          env1.FStar_Extraction_ML_UEnv.tcenv
                          (FStar_Syntax_Util.comp_effect_name c1)
                         in
                      let uu____2190 =
                        let uu____2197 =
                          FStar_TypeChecker_Env.effect_decl_opt
                            env1.FStar_Extraction_ML_UEnv.tcenv eff
                           in
                        FStar_Util.must uu____2197  in
                      match uu____2190 with
                      | (ed,qualifiers) ->
                          let uu____2218 =
                            FStar_All.pipe_right qualifiers
                              (FStar_List.contains
                                 FStar_Syntax_Syntax.Reifiable)
                             in
                          if uu____2218
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
                    let uu____2225 =
                      FStar_List.fold_right
                        (fun uu____2244  ->
                           fun uu____2245  ->
                             match (uu____2244, uu____2245) with
                             | ((uu____2266,t2),(tag,t')) ->
                                 (FStar_Extraction_ML_Syntax.E_PURE,
                                   (FStar_Extraction_ML_Syntax.MLTY_Fun
                                      (t2, tag, t')))) mlbs (erase1, t_ret)
                       in
                    (match uu____2225 with | (uu____2278,t2) -> t2)))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let res =
            let uu____2303 =
              let uu____2304 = FStar_Syntax_Util.un_uinst head1  in
              uu____2304.FStar_Syntax_Syntax.n  in
            match uu____2303 with
            | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
            | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv args
            | FStar_Syntax_Syntax.Tm_app (head2,args') ->
                let uu____2331 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app
                       (head2, (FStar_List.append args' args)))
                    FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   in
                term_as_mlty' env uu____2331
            | uu____2348 -> FStar_Extraction_ML_UEnv.unknownType  in
          res
      | FStar_Syntax_Syntax.Tm_abs (bs,ty,uu____2351) ->
          let uu____2372 = FStar_Syntax_Subst.open_term bs ty  in
          (match uu____2372 with
           | (bs1,ty1) ->
               let uu____2379 = binders_as_ml_binders env bs1  in
               (match uu____2379 with | (bts,env1) -> term_as_mlty' env1 ty1))
      | FStar_Syntax_Syntax.Tm_type uu____2404 ->
          FStar_Extraction_ML_UEnv.unknownType
      | FStar_Syntax_Syntax.Tm_let uu____2405 ->
          FStar_Extraction_ML_UEnv.unknownType
      | FStar_Syntax_Syntax.Tm_match uu____2418 ->
          FStar_Extraction_ML_UEnv.unknownType
<<<<<<< HEAD

and arg_as_mlty :
  FStar_Extraction_ML_UEnv.env ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 -> FStar_Extraction_ML_Syntax.mlty
  =
=======
and (arg_as_mlty
  :FStar_Extraction_ML_UEnv.env ->
     (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual)
       FStar_Pervasives_Native.tuple2 -> FStar_Extraction_ML_Syntax.mlty)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun g  ->
    fun uu____2442  ->
      match uu____2442 with
      | (a,uu____2448) ->
          let uu____2449 = is_type g a  in
          if uu____2449
          then term_as_mlty' g a
          else FStar_Extraction_ML_UEnv.erasedContent
<<<<<<< HEAD

and fv_app_as_mlty :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.args -> FStar_Extraction_ML_Syntax.mlty
  =
=======
and (fv_app_as_mlty
  :FStar_Extraction_ML_UEnv.env ->
     FStar_Syntax_Syntax.fv ->
       FStar_Syntax_Syntax.args -> FStar_Extraction_ML_Syntax.mlty)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun g  ->
    fun fv  ->
      fun args  ->
        let uu____2454 =
          let uu____2467 =
            FStar_TypeChecker_Env.lookup_lid g.FStar_Extraction_ML_UEnv.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____2467 with
          | ((uu____2488,fvty),uu____2490) ->
              let fvty1 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Normalize.UnfoldUntil
                     FStar_Syntax_Syntax.Delta_constant]
                  g.FStar_Extraction_ML_UEnv.tcenv fvty
                 in
              FStar_Syntax_Util.arrow_formals fvty1
           in
        match uu____2454 with
        | (formals,uu____2497) ->
            let mlargs = FStar_List.map (arg_as_mlty g) args  in
            let mlargs1 =
              let n_args = FStar_List.length args  in
              if (FStar_List.length formals) > n_args
              then
                let uu____2541 = FStar_Util.first_N n_args formals  in
                match uu____2541 with
                | (uu____2568,rest) ->
                    let uu____2594 =
                      FStar_List.map
                        (fun uu____2602  ->
                           FStar_Extraction_ML_UEnv.erasedContent) rest
                       in
                    FStar_List.append mlargs uu____2594
              else mlargs  in
            let nm =
              let uu____2609 =
                FStar_Extraction_ML_UEnv.maybe_mangle_type_projector g fv  in
              match uu____2609 with
              | FStar_Pervasives_Native.Some p -> p
              | FStar_Pervasives_Native.None  ->
                  FStar_Extraction_ML_Syntax.mlpath_of_lident
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            FStar_Extraction_ML_Syntax.MLTY_Named (mlargs1, nm)
<<<<<<< HEAD

and binders_as_ml_binders :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.binders ->
      ((FStar_Extraction_ML_Syntax.mlident,FStar_Extraction_ML_Syntax.mlty)
         FStar_Pervasives_Native.tuple2 Prims.list,FStar_Extraction_ML_UEnv.env)
        FStar_Pervasives_Native.tuple2
  =
=======
and (binders_as_ml_binders
  :FStar_Extraction_ML_UEnv.env ->
     FStar_Syntax_Syntax.binders ->
       ((FStar_Extraction_ML_Syntax.mlident,FStar_Extraction_ML_Syntax.mlty)
          FStar_Pervasives_Native.tuple2 Prims.list,FStar_Extraction_ML_UEnv.env)
         FStar_Pervasives_Native.tuple2)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun g  ->
    fun bs  ->
      let uu____2627 =
        FStar_All.pipe_right bs
          (FStar_List.fold_left
             (fun uu____2682  ->
                fun b  ->
                  match uu____2682 with
                  | (ml_bs,env) ->
                      let uu____2738 = is_type_binder g b  in
                      if uu____2738
                      then
                        let b1 = FStar_Pervasives_Native.fst b  in
                        let env1 =
                          FStar_Extraction_ML_UEnv.extend_ty env b1
                            (FStar_Pervasives_Native.Some
                               FStar_Extraction_ML_Syntax.MLTY_Top)
                           in
                        let ml_b =
                          let uu____2764 =
                            FStar_Extraction_ML_UEnv.bv_as_ml_termvar b1  in
                          (uu____2764, FStar_Extraction_ML_Syntax.ml_unit_ty)
                           in
                        ((ml_b :: ml_bs), env1)
                      else
                        (let b1 = FStar_Pervasives_Native.fst b  in
                         let t = term_as_mlty env b1.FStar_Syntax_Syntax.sort
                            in
                         let uu____2794 =
                           FStar_Extraction_ML_UEnv.extend_bv env b1 
                             ([], t) false false false
                            in
                         match uu____2794 with
                         | (env1,b2) ->
                             let ml_b =
<<<<<<< HEAD
                               let uu____2826 =
                                 FStar_Extraction_ML_UEnv.removeTick b2  in
                               (uu____2826, t)  in
                             ((ml_b :: ml_bs), env1))) ([], g))
         in
      match uu____2627 with | (ml_bs,env) -> ((FStar_List.rev ml_bs), env)

let mk_MLE_Seq :
  FStar_Extraction_ML_Syntax.mlexpr ->
    FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr'
  =
=======
                               let uu____2820 =
                                 FStar_Extraction_ML_UEnv.removeTick b2 in
                               (uu____2820, t) in
                             ((ml_b :: ml_bs), env1))) ([], g)) in
      match uu____2621 with | (ml_bs,env) -> ((FStar_List.rev ml_bs), env)
let (mk_MLE_Seq
  :FStar_Extraction_ML_Syntax.mlexpr ->
     FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr')=
>>>>>>> taramana_pointers_with_codes_modifies
  fun e1  ->
    fun e2  ->
      match ((e1.FStar_Extraction_ML_Syntax.expr),
              (e2.FStar_Extraction_ML_Syntax.expr))
      with
      | (FStar_Extraction_ML_Syntax.MLE_Seq
         es1,FStar_Extraction_ML_Syntax.MLE_Seq es2) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (FStar_List.append es1 es2)
      | (FStar_Extraction_ML_Syntax.MLE_Seq es1,uu____2936) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (FStar_List.append es1 [e2])
      | (uu____2939,FStar_Extraction_ML_Syntax.MLE_Seq es2) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (e1 :: es2)
<<<<<<< HEAD
      | uu____2943 -> FStar_Extraction_ML_Syntax.MLE_Seq [e1; e2]
  
let mk_MLE_Let :
  Prims.bool ->
    FStar_Extraction_ML_Syntax.mlletbinding ->
      FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr'
  =
=======
      | uu____2937 -> FStar_Extraction_ML_Syntax.MLE_Seq [e1; e2]
let (mk_MLE_Let
  :Prims.bool ->
     FStar_Extraction_ML_Syntax.mlletbinding ->
       FStar_Extraction_ML_Syntax.mlexpr ->
         FStar_Extraction_ML_Syntax.mlexpr')=
>>>>>>> taramana_pointers_with_codes_modifies
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
                    | uu____2975 when
                        (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
                          =
                          FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr
                        -> body.FStar_Extraction_ML_Syntax.expr
                    | uu____2976 ->
                        mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def
                          body)
<<<<<<< HEAD
             | uu____2977 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body))
        | uu____2980 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body)
  
let resugar_pat :
  FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option ->
    FStar_Extraction_ML_Syntax.mlpattern ->
      FStar_Extraction_ML_Syntax.mlpattern
  =
=======
             | uu____2971 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body))
        | uu____2974 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body)
let (resugar_pat
  :FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option ->
     FStar_Extraction_ML_Syntax.mlpattern ->
       FStar_Extraction_ML_Syntax.mlpattern)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun q  ->
    fun p  ->
      match p with
      | FStar_Extraction_ML_Syntax.MLP_CTor (d,pats) ->
          let uu____2999 = FStar_Extraction_ML_Util.is_xtuple d  in
          (match uu____2999 with
           | FStar_Pervasives_Native.Some n1 ->
               FStar_Extraction_ML_Syntax.MLP_Tuple pats
           | uu____3003 ->
               (match q with
                | FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Record_ctor (ty,fns)) ->
                    let path =
                      FStar_List.map FStar_Ident.text_of_id ty.FStar_Ident.ns
                       in
                    let fs = record_fields fns pats  in
                    FStar_Extraction_ML_Syntax.MLP_Record (path, fs)
<<<<<<< HEAD
                | uu____3030 -> p))
      | uu____3033 -> p
  
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
=======
                | uu____3024 -> p))
      | uu____3027 -> p
let rec (extract_one_pat
  :Prims.bool ->
     FStar_Extraction_ML_UEnv.env ->
       FStar_Syntax_Syntax.pat ->
         FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option ->
           (FStar_Extraction_ML_UEnv.env,(FStar_Extraction_ML_Syntax.mlpattern,
                                           FStar_Extraction_ML_Syntax.mlexpr
                                             Prims.list)
                                           FStar_Pervasives_Native.tuple2
                                           FStar_Pervasives_Native.option,
             Prims.bool) FStar_Pervasives_Native.tuple3)=
>>>>>>> taramana_pointers_with_codes_modifies
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
                     (fun uu____3092  ->
                        let uu____3093 =
                          FStar_Extraction_ML_Code.string_of_mlty
                            g.FStar_Extraction_ML_UEnv.currentModule t'
                           in
                        let uu____3094 =
                          FStar_Extraction_ML_Code.string_of_mlty
                            g.FStar_Extraction_ML_UEnv.currentModule t
                           in
                        FStar_Util.print2
                          "Expected pattern type %s; got pattern type %s\n"
                          uu____3093 uu____3094)
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
                let uu____3134 =
                  let uu____3135 =
                    let uu____3142 =
                      let uu____3145 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.ml_int_ty)
                          (FStar_Extraction_ML_Syntax.MLE_Var x)
                         in
                      let uu____3146 =
                        let uu____3149 =
                          let uu____3150 =
                            let uu____3151 =
                              FStar_Extraction_ML_Util.mlconst_of_const'
                                p.FStar_Syntax_Syntax.p i
                               in
                            FStar_All.pipe_left
                              (fun _0_43  ->
                                 FStar_Extraction_ML_Syntax.MLE_Const _0_43)
                              uu____3151
                             in
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty
                               FStar_Extraction_ML_Syntax.ml_int_ty)
                            uu____3150
                           in
                        [uu____3149]  in
                      uu____3145 :: uu____3146  in
                    (FStar_Extraction_ML_Util.prims_op_equality, uu____3142)
                     in
                  FStar_Extraction_ML_Syntax.MLE_App uu____3135  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     FStar_Extraction_ML_Syntax.ml_bool_ty) uu____3134
                 in
              let uu____3154 = ok FStar_Extraction_ML_Syntax.ml_int_ty  in
              (g,
                (FStar_Pervasives_Native.Some
                   ((FStar_Extraction_ML_Syntax.MLP_Var x), [when_clause])),
                uu____3154)
          | FStar_Syntax_Syntax.Pat_constant s ->
              let t =
                FStar_TypeChecker_TcTerm.tc_constant FStar_Range.dummyRange s
                 in
              let mlty = term_as_mlty g t  in
              let uu____3174 =
                let uu____3183 =
                  let uu____3190 =
                    let uu____3191 =
                      FStar_Extraction_ML_Util.mlconst_of_const'
                        p.FStar_Syntax_Syntax.p s
                       in
                    FStar_Extraction_ML_Syntax.MLP_Const uu____3191  in
                  (uu____3190, [])  in
                FStar_Pervasives_Native.Some uu____3183  in
              let uu____3200 = ok mlty  in (g, uu____3174, uu____3200)
          | FStar_Syntax_Syntax.Pat_var x ->
              let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort  in
              let uu____3211 =
                FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false false
                  imp
                 in
              (match uu____3211 with
               | (g1,x1) ->
                   let uu____3234 = ok mlty  in
                   (g1,
                     (if imp
                      then FStar_Pervasives_Native.None
                      else
                        FStar_Pervasives_Native.Some
                          ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                     uu____3234))
          | FStar_Syntax_Syntax.Pat_wild x ->
              let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort  in
              let uu____3268 =
                FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false false
                  imp
                 in
              (match uu____3268 with
               | (g1,x1) ->
                   let uu____3291 = ok mlty  in
                   (g1,
                     (if imp
                      then FStar_Pervasives_Native.None
                      else
                        FStar_Pervasives_Native.Some
                          ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                     uu____3291))
          | FStar_Syntax_Syntax.Pat_dot_term uu____3323 ->
              (g, FStar_Pervasives_Native.None, true)
          | FStar_Syntax_Syntax.Pat_cons (f,pats) ->
              let uu____3362 =
                let uu____3367 = FStar_Extraction_ML_UEnv.lookup_fv g f  in
                match uu____3367 with
                | FStar_Util.Inr
                    (uu____3372,{
                                  FStar_Extraction_ML_Syntax.expr =
                                    FStar_Extraction_ML_Syntax.MLE_Name n1;
                                  FStar_Extraction_ML_Syntax.mlty =
                                    uu____3374;
                                  FStar_Extraction_ML_Syntax.loc = uu____3375;_},ttys,uu____3377)
                    -> (n1, ttys)
                | uu____3390 -> failwith "Expected a constructor"  in
              (match uu____3362 with
               | (d,tys) ->
                   let nTyVars =
                     FStar_List.length (FStar_Pervasives_Native.fst tys)  in
                   let uu____3412 = FStar_Util.first_N nTyVars pats  in
                   (match uu____3412 with
                    | (tysVarPats,restPats) ->
                        let f_ty_opt =
                          try
                            let mlty_args =
                              FStar_All.pipe_right tysVarPats
                                (FStar_List.map
                                   (fun uu____3545  ->
                                      match uu____3545 with
                                      | (p1,uu____3553) ->
                                          (match p1.FStar_Syntax_Syntax.v
                                           with
                                           | FStar_Syntax_Syntax.Pat_dot_term
                                               (uu____3558,t) ->
                                               term_as_mlty g t
                                           | uu____3564 ->
                                               (FStar_Extraction_ML_UEnv.debug
                                                  g
                                                  (fun uu____3568  ->
                                                     let uu____3569 =
                                                       FStar_Syntax_Print.pat_to_string
                                                         p1
                                                        in
                                                     FStar_Util.print1
                                                       "Pattern %s is not extractable"
                                                       uu____3569);
                                                FStar_Exn.raise
                                                  Un_extractable))))
                               in
                            let f_ty =
                              FStar_Extraction_ML_Util.subst tys mlty_args
                               in
                            let uu____3571 =
                              FStar_Extraction_ML_Util.uncurry_mlty_fun f_ty
                               in
                            FStar_Pervasives_Native.Some uu____3571
                          with
                          | Un_extractable  -> FStar_Pervasives_Native.None
                           in
                        let uu____3600 =
                          FStar_Util.fold_map
                            (fun g1  ->
                               fun uu____3636  ->
                                 match uu____3636 with
                                 | (p1,imp1) ->
                                     let uu____3655 =
                                       extract_one_pat true g1 p1
                                         FStar_Pervasives_Native.None
                                        in
                                     (match uu____3655 with
                                      | (g2,p2,uu____3684) -> (g2, p2))) g
                            tysVarPats
                           in
                        (match uu____3600 with
                         | (g1,tyMLPats) ->
                             let uu____3745 =
                               FStar_Util.fold_map
                                 (fun uu____3809  ->
                                    fun uu____3810  ->
                                      match (uu____3809, uu____3810) with
                                      | ((g2,f_ty_opt1),(p1,imp1)) ->
                                          let uu____3903 =
                                            match f_ty_opt1 with
                                            | FStar_Pervasives_Native.Some
                                                (hd1::rest,res) ->
                                                ((FStar_Pervasives_Native.Some
                                                    (rest, res)),
                                                  (FStar_Pervasives_Native.Some
                                                     hd1))
                                            | uu____3963 ->
                                                (FStar_Pervasives_Native.None,
                                                  FStar_Pervasives_Native.None)
                                             in
                                          (match uu____3903 with
                                           | (f_ty_opt2,expected_ty) ->
                                               let uu____4034 =
                                                 extract_one_pat false g2 p1
                                                   expected_ty
                                                  in
                                               (match uu____4034 with
                                                | (g3,p2,uu____4075) ->
                                                    ((g3, f_ty_opt2), p2))))
                                 (g1, f_ty_opt) restPats
                                in
                             (match uu____3745 with
                              | ((g2,f_ty_opt1),restMLPats) ->
                                  let uu____4193 =
                                    let uu____4204 =
                                      FStar_All.pipe_right
                                        (FStar_List.append tyMLPats
                                           restMLPats)
                                        (FStar_List.collect
                                           (fun uu___142_4255  ->
                                              match uu___142_4255 with
                                              | FStar_Pervasives_Native.Some
                                                  x -> [x]
                                              | uu____4297 -> []))
                                       in
                                    FStar_All.pipe_right uu____4204
                                      FStar_List.split
                                     in
                                  (match uu____4193 with
                                   | (mlPats,when_clauses) ->
                                       let pat_ty_compat =
                                         match f_ty_opt1 with
                                         | FStar_Pervasives_Native.Some
                                             ([],t) -> ok t
                                         | uu____4370 -> false  in
                                       let uu____4379 =
                                         let uu____4388 =
                                           let uu____4395 =
                                             resugar_pat
                                               f.FStar_Syntax_Syntax.fv_qual
                                               (FStar_Extraction_ML_Syntax.MLP_CTor
                                                  (d, mlPats))
                                              in
                                           let uu____4398 =
                                             FStar_All.pipe_right
                                               when_clauses
                                               FStar_List.flatten
                                              in
                                           (uu____4395, uu____4398)  in
                                         FStar_Pervasives_Native.Some
<<<<<<< HEAD
                                           uu____4388
                                          in
                                       (g2, uu____4379, pat_ty_compat))))))
  
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
=======
                                           uu____4382 in
                                       (g2, uu____4373, pat_ty_compat))))))
let (extract_pat
  :FStar_Extraction_ML_UEnv.env ->
     FStar_Syntax_Syntax.pat ->
       FStar_Extraction_ML_Syntax.mlty ->
         (FStar_Extraction_ML_UEnv.env,(FStar_Extraction_ML_Syntax.mlpattern,
                                         FStar_Extraction_ML_Syntax.mlexpr
                                           FStar_Pervasives_Native.option)
                                         FStar_Pervasives_Native.tuple2
                                         Prims.list,Prims.bool)
           FStar_Pervasives_Native.tuple3)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun g  ->
    fun p  ->
      fun expected_t  ->
        let extract_one_pat1 g1 p1 expected_t1 =
          let uu____4489 = extract_one_pat false g1 p1 expected_t1  in
          match uu____4489 with
          | (g2,FStar_Pervasives_Native.Some (x,v1),b) -> (g2, (x, v1), b)
          | uu____4546 -> failwith "Impossible: Unable to translate pattern"
           in
        let mk_when_clause whens =
          match whens with
          | [] -> FStar_Pervasives_Native.None
          | hd1::tl1 ->
              let uu____4589 =
                FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd1 tl1
                 in
              FStar_Pervasives_Native.Some uu____4589
           in
        let uu____4590 =
          extract_one_pat1 g p (FStar_Pervasives_Native.Some expected_t)  in
        match uu____4590 with
        | (g1,(p1,whens),b) ->
            let when_clause = mk_when_clause whens  in
            (g1, [(p1, when_clause)], b)
<<<<<<< HEAD
  
let maybe_eta_data_and_project_record :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option ->
      FStar_Extraction_ML_Syntax.mlty ->
        FStar_Extraction_ML_Syntax.mlexpr ->
          FStar_Extraction_ML_Syntax.mlexpr
  =
=======
let (maybe_eta_data_and_project_record
  :FStar_Extraction_ML_UEnv.env ->
     FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option ->
       FStar_Extraction_ML_Syntax.mlty ->
         FStar_Extraction_ML_Syntax.mlexpr ->
           FStar_Extraction_ML_Syntax.mlexpr)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun g  ->
    fun qual  ->
      fun residualType  ->
        fun mlAppExpr  ->
          let rec eta_args more_args t =
            match t with
            | FStar_Extraction_ML_Syntax.MLTY_Fun (t0,uu____4732,t1) ->
                let x = FStar_Extraction_ML_Syntax.gensym ()  in
                let uu____4735 =
                  let uu____4746 =
                    let uu____4755 =
                      FStar_All.pipe_left
                        (FStar_Extraction_ML_Syntax.with_ty t0)
                        (FStar_Extraction_ML_Syntax.MLE_Var x)
                       in
                    ((x, t0), uu____4755)  in
                  uu____4746 :: more_args  in
                eta_args uu____4735 t1
            | FStar_Extraction_ML_Syntax.MLTY_Named (uu____4768,uu____4769)
                -> ((FStar_List.rev more_args), t)
            | uu____4792 -> failwith "Impossible: Head type is not an arrow"
             in
          let as_record qual1 e =
            match ((e.FStar_Extraction_ML_Syntax.expr), qual1) with
            | (FStar_Extraction_ML_Syntax.MLE_CTor
               (uu____4820,args),FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Record_ctor (tyname,fields))) ->
                let path =
                  FStar_List.map FStar_Ident.text_of_id tyname.FStar_Ident.ns
                   in
                let fields1 = record_fields fields args  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     e.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_Record (path, fields1))
            | uu____4852 -> e  in
          let resugar_and_maybe_eta qual1 e =
            let uu____4870 = eta_args [] residualType  in
            match uu____4870 with
            | (eargs,tres) ->
                (match eargs with
                 | [] ->
                     let uu____4923 = as_record qual1 e  in
                     FStar_Extraction_ML_Util.resugar_exp uu____4923
                 | uu____4924 ->
                     let uu____4935 = FStar_List.unzip eargs  in
                     (match uu____4935 with
                      | (binders,eargs1) ->
                          (match e.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_CTor (head1,args)
                               ->
                               let body =
                                 let uu____4977 =
                                   let uu____4978 =
                                     FStar_All.pipe_left
                                       (FStar_Extraction_ML_Syntax.with_ty
                                          tres)
                                       (FStar_Extraction_ML_Syntax.MLE_CTor
                                          (head1,
                                            (FStar_List.append args eargs1)))
                                      in
                                   FStar_All.pipe_left (as_record qual1)
                                     uu____4978
                                    in
                                 FStar_All.pipe_left
                                   FStar_Extraction_ML_Util.resugar_exp
                                   uu____4977
                                  in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    e.FStar_Extraction_ML_Syntax.mlty)
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    (binders, body))
                           | uu____4987 ->
                               failwith "Impossible: Not a constructor")))
             in
          match ((mlAppExpr.FStar_Extraction_ML_Syntax.expr), qual) with
          | (uu____4990,FStar_Pervasives_Native.None ) -> mlAppExpr
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____4994;
                FStar_Extraction_ML_Syntax.loc = uu____4995;_},mle::args),FStar_Pervasives_Native.Some
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
                | uu____5022 ->
                    let uu____5025 =
                      let uu____5032 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj
                         in
                      (uu____5032, args)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____5025
                 in
              FStar_Extraction_ML_Syntax.with_ty
                mlAppExpr.FStar_Extraction_ML_Syntax.mlty e
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____5036;
                     FStar_Extraction_ML_Syntax.loc = uu____5037;_},uu____5038);
                FStar_Extraction_ML_Syntax.mlty = uu____5039;
                FStar_Extraction_ML_Syntax.loc = uu____5040;_},mle::args),FStar_Pervasives_Native.Some
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
                | uu____5071 ->
                    let uu____5074 =
                      let uu____5081 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj
                         in
                      (uu____5081, args)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____5074
                 in
              FStar_Extraction_ML_Syntax.with_ty
                mlAppExpr.FStar_Extraction_ML_Syntax.mlty e
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____5085;
                FStar_Extraction_ML_Syntax.loc = uu____5086;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____5094 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5094
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____5098;
                FStar_Extraction_ML_Syntax.loc = uu____5099;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____5101)) ->
              let uu____5114 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5114
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____5118;
                     FStar_Extraction_ML_Syntax.loc = uu____5119;_},uu____5120);
                FStar_Extraction_ML_Syntax.mlty = uu____5121;
                FStar_Extraction_ML_Syntax.loc = uu____5122;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____5134 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5134
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____5138;
                     FStar_Extraction_ML_Syntax.loc = uu____5139;_},uu____5140);
                FStar_Extraction_ML_Syntax.mlty = uu____5141;
                FStar_Extraction_ML_Syntax.loc = uu____5142;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____5144)) ->
              let uu____5161 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5161
          | (FStar_Extraction_ML_Syntax.MLE_Name
             mlp,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor
             )) ->
              let uu____5167 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5167
          | (FStar_Extraction_ML_Syntax.MLE_Name
             mlp,FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____5171)) ->
              let uu____5180 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5180
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____5184;
                FStar_Extraction_ML_Syntax.loc = uu____5185;_},uu____5186),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____5193 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
<<<<<<< HEAD
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5193
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____5197;
                FStar_Extraction_ML_Syntax.loc = uu____5198;_},uu____5199),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____5200)) ->
              let uu____5213 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5213
          | uu____5216 -> mlAppExpr
  
let maybe_downgrade_eff :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.e_tag ->
      FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.e_tag
  =
=======
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, [])) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5078
          | uu____5081 -> mlAppExpr
let (maybe_downgrade_eff
  :FStar_Extraction_ML_UEnv.env ->
     FStar_Extraction_ML_Syntax.e_tag ->
       FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.e_tag)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun g  ->
    fun f  ->
      fun t  ->
        let uu____5235 =
          (f = FStar_Extraction_ML_Syntax.E_GHOST) &&
<<<<<<< HEAD
            (type_leq g t FStar_Extraction_ML_Syntax.ml_unit_ty)
           in
        if uu____5235 then FStar_Extraction_ML_Syntax.E_PURE else f
  
let rec term_as_mlexpr :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Extraction_ML_Syntax.mlexpr,FStar_Extraction_ML_Syntax.e_tag,
        FStar_Extraction_ML_Syntax.mlty) FStar_Pervasives_Native.tuple3
  =
=======
            (type_leq g t FStar_Extraction_ML_Syntax.ml_unit_ty) in
        if uu____5100 then FStar_Extraction_ML_Syntax.E_PURE else f
let rec (term_as_mlexpr
  :FStar_Extraction_ML_UEnv.env ->
     FStar_Syntax_Syntax.term ->
       (FStar_Extraction_ML_Syntax.mlexpr,FStar_Extraction_ML_Syntax.e_tag,
         FStar_Extraction_ML_Syntax.mlty) FStar_Pervasives_Native.tuple3)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun g  ->
    fun t  ->
      let uu____5289 = term_as_mlexpr' g t  in
      match uu____5289 with
      | (e,tag,ty) ->
          let tag1 = maybe_downgrade_eff g tag ty  in
          (FStar_Extraction_ML_UEnv.debug g
             (fun u  ->
                let uu____5310 =
                  let uu____5311 = FStar_Syntax_Print.tag_of_term t  in
                  let uu____5312 = FStar_Syntax_Print.term_to_string t  in
                  let uu____5313 =
                    FStar_Extraction_ML_Code.string_of_mlty
                      g.FStar_Extraction_ML_UEnv.currentModule ty
                     in
                  FStar_Util.format4
                    "term_as_mlexpr (%s) :  %s has ML type %s and effect %s\n"
                    uu____5311 uu____5312 uu____5313
                    (FStar_Extraction_ML_Util.eff_to_string tag1)
                   in
                FStar_Util.print_string uu____5310);
           erase g e ty tag1)
<<<<<<< HEAD

and check_term_as_mlexpr :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Extraction_ML_Syntax.e_tag ->
        FStar_Extraction_ML_Syntax.mlty ->
          (FStar_Extraction_ML_Syntax.mlexpr,FStar_Extraction_ML_Syntax.mlty)
            FStar_Pervasives_Native.tuple2
  =
=======
and (check_term_as_mlexpr
  :FStar_Extraction_ML_UEnv.env ->
     FStar_Syntax_Syntax.term ->
       FStar_Extraction_ML_Syntax.e_tag ->
         FStar_Extraction_ML_Syntax.mlty ->
           (FStar_Extraction_ML_Syntax.mlexpr,FStar_Extraction_ML_Syntax.mlty)
             FStar_Pervasives_Native.tuple2)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun g  ->
    fun t  ->
      fun f  ->
        fun ty  ->
          let uu____5322 = check_term_as_mlexpr' g t f ty  in
          match uu____5322 with
          | (e,t1) ->
<<<<<<< HEAD
              let uu____5333 = erase g e t1 f  in
              (match uu____5333 with | (r,uu____5345,t2) -> (r, t2))

and check_term_as_mlexpr' :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Extraction_ML_Syntax.e_tag ->
        FStar_Extraction_ML_Syntax.mlty ->
          (FStar_Extraction_ML_Syntax.mlexpr,FStar_Extraction_ML_Syntax.mlty)
            FStar_Pervasives_Native.tuple2
  =
=======
              let uu____5198 = erase g e t1 f in
              (match uu____5198 with | (r,uu____5210,t2) -> (r, t2))
and (check_term_as_mlexpr'
  :FStar_Extraction_ML_UEnv.env ->
     FStar_Syntax_Syntax.term ->
       FStar_Extraction_ML_Syntax.e_tag ->
         FStar_Extraction_ML_Syntax.mlty ->
           (FStar_Extraction_ML_Syntax.mlexpr,FStar_Extraction_ML_Syntax.mlty)
             FStar_Pervasives_Native.tuple2)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun g  ->
    fun e0  ->
      fun f  ->
        fun ty  ->
          let uu____5355 = term_as_mlexpr g e0  in
          match uu____5355 with
          | (e,tag,t) ->
              let tag1 = maybe_downgrade_eff g tag t  in
              if FStar_Extraction_ML_Util.eff_leq tag1 f
              then
                let uu____5374 = maybe_coerce g e t ty  in (uu____5374, ty)
              else err_unexpected_eff e0 f tag1
<<<<<<< HEAD

and term_as_mlexpr' :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Extraction_ML_Syntax.mlexpr,FStar_Extraction_ML_Syntax.e_tag,
        FStar_Extraction_ML_Syntax.mlty) FStar_Pervasives_Native.tuple3
  =
=======
and (term_as_mlexpr'
  :FStar_Extraction_ML_UEnv.env ->
     FStar_Syntax_Syntax.term ->
       (FStar_Extraction_ML_Syntax.mlexpr,FStar_Extraction_ML_Syntax.e_tag,
         FStar_Extraction_ML_Syntax.mlty) FStar_Pervasives_Native.tuple3)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun g  ->
    fun top  ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u  ->
           let uu____5392 =
             let uu____5393 =
               FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos  in
             let uu____5394 = FStar_Syntax_Print.tag_of_term top  in
             let uu____5395 = FStar_Syntax_Print.term_to_string top  in
             FStar_Util.format3 "%s: term_as_mlexpr' (%s) :  %s \n"
               uu____5393 uu____5394 uu____5395
              in
           FStar_Util.print_string uu____5392);
      (let t = FStar_Syntax_Subst.compress top  in
       match t.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____5403 =
             let uu____5404 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5404
              in
           failwith uu____5403
       | FStar_Syntax_Syntax.Tm_delayed uu____5411 ->
           let uu____5436 =
             let uu____5437 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5437
              in
           failwith uu____5436
       | FStar_Syntax_Syntax.Tm_uvar uu____5444 ->
           let uu____5461 =
             let uu____5462 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5462
              in
           failwith uu____5461
       | FStar_Syntax_Syntax.Tm_bvar uu____5469 ->
           let uu____5470 =
             let uu____5471 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5471
              in
           failwith uu____5470
       | FStar_Syntax_Syntax.Tm_type uu____5478 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_refine uu____5479 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_arrow uu____5486 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Mutable_alloc ))
           ->
           let uu____5504 = term_as_mlexpr' g t1  in
           (match uu____5504 with
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
            | uu____5550 -> failwith "impossible")
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_monadic (m,uu____5565)) ->
           let t2 = FStar_Syntax_Subst.compress t1  in
           (match t2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) when
                FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname ->
                let uu____5595 =
                  let uu____5602 =
                    FStar_TypeChecker_Env.effect_decl_opt
                      g.FStar_Extraction_ML_UEnv.tcenv m
                     in
                  FStar_Util.must uu____5602  in
                (match uu____5595 with
                 | (ed,qualifiers) ->
                     let uu____5629 =
                       let uu____5630 =
                         FStar_All.pipe_right qualifiers
                           (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                          in
                       FStar_All.pipe_right uu____5630 Prims.op_Negation  in
                     if uu____5629
                     then term_as_mlexpr' g t2
                     else
                       failwith
                         "This should not happen (should have been handled at Tm_abs level)")
            | uu____5646 -> term_as_mlexpr' g t2)
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____5648) -> term_as_mlexpr' g t1
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____5654) -> term_as_mlexpr' g t1
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____5660 =
             FStar_TypeChecker_TcTerm.type_of_tot_term
               g.FStar_Extraction_ML_UEnv.tcenv t
              in
           (match uu____5660 with
            | (uu____5673,ty,uu____5675) ->
                let ml_ty = term_as_mlty g ty  in
                let uu____5677 =
                  let uu____5678 =
                    let uu____5679 =
                      FStar_Extraction_ML_Util.mlconst_of_const'
                        t.FStar_Syntax_Syntax.pos c
                       in
                    FStar_All.pipe_left
                      (fun _0_44  ->
                         FStar_Extraction_ML_Syntax.MLE_Const _0_44)
                      uu____5679
                     in
                  FStar_Extraction_ML_Syntax.with_ty ml_ty uu____5678  in
                (uu____5677, FStar_Extraction_ML_Syntax.E_PURE, ml_ty))
       | FStar_Syntax_Syntax.Tm_name uu____5680 ->
           let uu____5681 = is_type g t  in
           if uu____5681
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____5689 = FStar_Extraction_ML_UEnv.lookup_term g t  in
              match uu____5689 with
              | (FStar_Util.Inl uu____5702,uu____5703) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | (FStar_Util.Inr (uu____5740,x,mltys,uu____5743),qual) ->
                  (match mltys with
                   | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                       ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | ([],t1) ->
                       let uu____5789 =
                         maybe_eta_data_and_project_record g qual t1 x  in
                       (uu____5789, FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | uu____5790 -> err_uninst g t mltys t))
       | FStar_Syntax_Syntax.Tm_fvar uu____5797 ->
           let uu____5798 = is_type g t  in
           if uu____5798
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____5806 = FStar_Extraction_ML_UEnv.lookup_term g t  in
              match uu____5806 with
              | (FStar_Util.Inl uu____5819,uu____5820) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | (FStar_Util.Inr (uu____5857,x,mltys,uu____5860),qual) ->
                  (match mltys with
                   | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                       ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | ([],t1) ->
                       let uu____5906 =
                         maybe_eta_data_and_project_record g qual t1 x  in
                       (uu____5906, FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | uu____5907 -> err_uninst g t mltys t))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,copt) ->
           let uu____5937 = FStar_Syntax_Subst.open_term bs body  in
           (match uu____5937 with
            | (bs1,body1) ->
                let uu____5950 = binders_as_ml_binders g bs1  in
                (match uu____5950 with
                 | (ml_bs,env) ->
                     let body2 =
                       match copt with
                       | FStar_Pervasives_Native.Some c ->
                           let uu____5983 =
                             FStar_TypeChecker_Env.is_reifiable
                               env.FStar_Extraction_ML_UEnv.tcenv c
                              in
                           if uu____5983
                           then
                             FStar_TypeChecker_Util.reify_body
                               env.FStar_Extraction_ML_UEnv.tcenv body1
                           else body1
                       | FStar_Pervasives_Native.None  ->
                           (FStar_Extraction_ML_UEnv.debug g
                              (fun uu____5988  ->
                                 let uu____5989 =
                                   FStar_Syntax_Print.term_to_string body1
                                    in
                                 FStar_Util.print1
                                   "No computation type for: %s\n" uu____5989);
                            body1)
                        in
                     let uu____5990 = term_as_mlexpr env body2  in
                     (match uu____5990 with
                      | (ml_body,f,t1) ->
                          let uu____6006 =
                            FStar_List.fold_right
                              (fun uu____6025  ->
                                 fun uu____6026  ->
                                   match (uu____6025, uu____6026) with
                                   | ((uu____6047,targ),(f1,t2)) ->
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         (FStar_Extraction_ML_Syntax.MLTY_Fun
                                            (targ, f1, t2)))) ml_bs (f, t1)
                             in
                          (match uu____6006 with
                           | (f1,tfun) ->
                               let uu____6067 =
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty tfun)
                                   (FStar_Extraction_ML_Syntax.MLE_Fun
                                      (ml_bs, ml_body))
                                  in
                               (uu____6067, f1, tfun)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____6074);
              FStar_Syntax_Syntax.pos = uu____6075;
              FStar_Syntax_Syntax.vars = uu____6076;_},uu____6077)
           -> failwith "Unreachable? Tm_app Const_reflect"
       | FStar_Syntax_Syntax.Tm_app (head1,uu____6105::(v1,uu____6107)::[])
           when (FStar_Syntax_Util.is_fstar_tactics_embed head1) && false ->
           let uu____6148 =
             let uu____6151 = FStar_Syntax_Print.term_to_string v1  in
             FStar_Util.format2 "Trying to extract a quotation of %s"
               uu____6151
              in
           let s =
             let uu____6153 =
               let uu____6154 =
                 let uu____6155 =
                   let uu____6158 = FStar_Util.marshal v1  in
                   FStar_Util.bytes_of_string uu____6158  in
                 FStar_Extraction_ML_Syntax.MLC_Bytes uu____6155  in
               FStar_Extraction_ML_Syntax.MLE_Const uu____6154  in
             FStar_Extraction_ML_Syntax.with_ty
               FStar_Extraction_ML_Syntax.ml_string_ty uu____6153
              in
           let zero1 =
             FStar_Extraction_ML_Syntax.with_ty
               FStar_Extraction_ML_Syntax.ml_int_ty
               (FStar_Extraction_ML_Syntax.MLE_Const
                  (FStar_Extraction_ML_Syntax.MLC_Int
                     ("0", FStar_Pervasives_Native.None)))
              in
           let term_ty =
             let uu____6173 =
               FStar_Syntax_Syntax.fvar
                 FStar_Parser_Const.fstar_syntax_syntax_term
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None
                in
             term_as_mlty g uu____6173  in
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
           let uu____6178 =
             FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty term_ty)
               (FStar_Extraction_ML_Syntax.MLE_App
                  (marshal_from_string, [s; zero1]))
              in
           (uu____6178, FStar_Extraction_ML_Syntax.E_PURE, term_ty)
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let is_total rc =
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_Tot_lid)
               ||
               (FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
                  (FStar_List.existsb
                     (fun uu___143_6210  ->
                        match uu___143_6210 with
                        | FStar_Syntax_Syntax.TOTAL  -> true
                        | uu____6211 -> false)))
              in
           let uu____6212 =
             let uu____6217 =
               let uu____6218 = FStar_Syntax_Subst.compress head1  in
               uu____6218.FStar_Syntax_Syntax.n  in
             ((head1.FStar_Syntax_Syntax.n), uu____6217)  in
           (match uu____6212 with
            | (FStar_Syntax_Syntax.Tm_uvar uu____6227,uu____6228) ->
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
            | (uu____6246,FStar_Syntax_Syntax.Tm_abs
               (bs,uu____6248,FStar_Pervasives_Native.Some rc)) when
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
            | (uu____6269,FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_reify )) ->
                let e =
                  let uu____6271 = FStar_List.hd args  in
                  FStar_TypeChecker_Util.reify_body_with_arg
                    g.FStar_Extraction_ML_UEnv.tcenv head1 uu____6271
                   in
                let tm =
                  let uu____6281 =
                    let uu____6282 = FStar_TypeChecker_Util.remove_reify e
                       in
                    let uu____6283 = FStar_List.tl args  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____6282 uu____6283  in
                  uu____6281 FStar_Pervasives_Native.None
                    t.FStar_Syntax_Syntax.pos
                   in
                term_as_mlexpr' g tm
            | uu____6292 ->
                let rec extract_app is_data uu____6337 uu____6338 restArgs =
                  match (uu____6337, uu____6338) with
                  | ((mlhead,mlargs_f),(f,t1)) ->
                      (match (restArgs, t1) with
                       | ([],uu____6428) ->
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
                                | uu____6450 -> false)
                              in
                           let uu____6451 =
                             if evaluation_order_guaranteed
                             then
                               let uu____6476 =
                                 FStar_All.pipe_right
                                   (FStar_List.rev mlargs_f)
                                   (FStar_List.map
                                      FStar_Pervasives_Native.fst)
                                  in
                               ([], uu____6476)
                             else
                               FStar_List.fold_left
                                 (fun uu____6530  ->
                                    fun uu____6531  ->
                                      match (uu____6530, uu____6531) with
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
                                             let uu____6634 =
                                               let uu____6637 =
                                                 FStar_All.pipe_left
                                                   (FStar_Extraction_ML_Syntax.with_ty
                                                      arg.FStar_Extraction_ML_Syntax.mlty)
                                                   (FStar_Extraction_ML_Syntax.MLE_Var
                                                      x)
                                                  in
                                               uu____6637 :: out_args  in
                                             (((x, arg) :: lbs), uu____6634)))
                                 ([], []) mlargs_f
                              in
                           (match uu____6451 with
                            | (lbs,mlargs) ->
                                let app =
                                  let uu____6687 =
                                    FStar_All.pipe_left
                                      (FStar_Extraction_ML_Syntax.with_ty t1)
                                      (FStar_Extraction_ML_Syntax.MLE_App
                                         (mlhead, mlargs))
                                     in
                                  FStar_All.pipe_left
                                    (maybe_eta_data_and_project_record g
                                       is_data t1) uu____6687
                                   in
                                let l_app =
                                  FStar_List.fold_right
                                    (fun uu____6699  ->
                                       fun out  ->
                                         match uu____6699 with
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
                       | ((arg,uu____6720)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                          (formal_t,f',t2)) when
                           (is_type g arg) &&
                             (type_leq g formal_t
                                FStar_Extraction_ML_Syntax.ml_unit_ty)
                           ->
                           let uu____6751 =
                             let uu____6756 =
                               FStar_Extraction_ML_Util.join
                                 arg.FStar_Syntax_Syntax.pos f f'
                                in
                             (uu____6756, t2)  in
                           extract_app is_data
                             (mlhead,
                               ((FStar_Extraction_ML_Syntax.ml_unit,
                                  FStar_Extraction_ML_Syntax.E_PURE) ::
                               mlargs_f)) uu____6751 rest
                       | ((e0,uu____6768)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                          (tExpected,f',t2)) ->
                           let r = e0.FStar_Syntax_Syntax.pos  in
                           let uu____6800 = term_as_mlexpr g e0  in
                           (match uu____6800 with
                            | (e01,f0,tInferred) ->
                                let e02 =
                                  maybe_coerce g e01 tInferred tExpected  in
                                let uu____6817 =
                                  let uu____6822 =
                                    FStar_Extraction_ML_Util.join_l r
                                      [f; f'; f0]
                                     in
                                  (uu____6822, t2)  in
                                extract_app is_data
                                  (mlhead, ((e02, f0) :: mlargs_f))
                                  uu____6817 rest)
                       | uu____6833 ->
                           let uu____6846 =
                             FStar_Extraction_ML_Util.udelta_unfold g t1  in
                           (match uu____6846 with
                            | FStar_Pervasives_Native.Some t2 ->
                                extract_app is_data (mlhead, mlargs_f)
                                  (f, t2) restArgs
                            | FStar_Pervasives_Native.None  ->
                                err_ill_typed_application g top restArgs t1))
                   in
                let extract_app_maybe_projector is_data mlhead uu____6903
                  args1 =
                  match uu____6903 with
                  | (f,t1) ->
                      (match is_data with
                       | FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_projector uu____6935)
                           ->
                           let rec remove_implicits args2 f1 t2 =
                             match (args2, t2) with
                             | ((a0,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____7013))::args3,FStar_Extraction_ML_Syntax.MLTY_Fun
                                (uu____7015,f',t3)) ->
                                 let uu____7052 =
                                   FStar_Extraction_ML_Util.join
                                     a0.FStar_Syntax_Syntax.pos f1 f'
                                    in
                                 remove_implicits args3 uu____7052 t3
                             | uu____7053 -> (args2, f1, t2)  in
                           let uu____7078 = remove_implicits args1 f t1  in
                           (match uu____7078 with
                            | (args2,f1,t2) ->
                                extract_app is_data (mlhead, []) (f1, t2)
                                  args2)
                       | uu____7134 ->
                           extract_app is_data (mlhead, []) (f, t1) args1)
                   in
                let uu____7147 = is_type g t  in
                if uu____7147
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
                         (let uu____7164 =
                            let uu____7165 =
                              FStar_Extraction_ML_Syntax.string_of_mlpath
                                g.FStar_Extraction_ML_UEnv.currentModule
                               in
                            uu____7165 = "FStar.Tactics.Builtins"  in
                          Prims.op_Negation uu____7164)
                       ->
                       (match args with
                        | a::b::[] ->
                            term_as_mlexpr g (FStar_Pervasives_Native.fst a)
                        | uu____7206 ->
                            let uu____7215 =
                              FStar_Syntax_Print.args_to_string args  in
                            failwith uu____7215)
                   | FStar_Syntax_Syntax.Tm_name uu____7222 ->
                       let uu____7223 =
                         let uu____7236 =
                           FStar_Extraction_ML_UEnv.lookup_term g head2  in
                         match uu____7236 with
                         | (FStar_Util.Inr (uu____7255,x1,x2,x3),q) ->
                             ((x1, x2, x3), q)
                         | uu____7300 -> failwith "FIXME Ty"  in
                       (match uu____7223 with
                        | ((head_ml,(vars,t1),inst_ok),qual) ->
                            let has_typ_apps =
                              match args with
                              | (a,uu____7350)::uu____7351 -> is_type g a
                              | uu____7370 -> false  in
                            let uu____7379 =
                              match vars with
                              | uu____7408::uu____7409 when
                                  (Prims.op_Negation has_typ_apps) && inst_ok
                                  -> (head_ml, t1, args)
                              | uu____7420 ->
                                  let n1 = FStar_List.length vars  in
                                  if n1 <= (FStar_List.length args)
                                  then
                                    let uu____7448 =
                                      FStar_Util.first_N n1 args  in
                                    (match uu____7448 with
                                     | (prefix1,rest) ->
                                         let prefixAsMLTypes =
                                           FStar_List.map
                                             (fun uu____7537  ->
                                                match uu____7537 with
                                                | (x,uu____7543) ->
                                                    term_as_mlty g x) prefix1
                                            in
                                         let t2 =
                                           instantiate (vars, t1)
                                             prefixAsMLTypes
                                            in
                                         let mk_tapp e ty_args =
                                           match ty_args with
                                           | [] -> e
                                           | uu____7556 ->
                                               let uu___147_7559 = e  in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (FStar_Extraction_ML_Syntax.MLE_TApp
                                                      (e, ty_args));
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   =
                                                   (uu___147_7559.FStar_Extraction_ML_Syntax.mlty);
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___147_7559.FStar_Extraction_ML_Syntax.loc)
                                               }
                                            in
                                         let head3 =
                                           match head_ml.FStar_Extraction_ML_Syntax.expr
                                           with
                                           | FStar_Extraction_ML_Syntax.MLE_Name
                                               uu____7563 ->
                                               let uu___148_7564 =
                                                 mk_tapp head_ml
                                                   prefixAsMLTypes
                                                  in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (uu___148_7564.FStar_Extraction_ML_Syntax.expr);
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   = t2;
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___148_7564.FStar_Extraction_ML_Syntax.loc)
                                               }
                                           | FStar_Extraction_ML_Syntax.MLE_Var
                                               uu____7565 ->
                                               let uu___148_7566 =
                                                 mk_tapp head_ml
                                                   prefixAsMLTypes
                                                  in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (uu___148_7566.FStar_Extraction_ML_Syntax.expr);
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   = t2;
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___148_7566.FStar_Extraction_ML_Syntax.loc)
                                               }
                                           | FStar_Extraction_ML_Syntax.MLE_App
                                               (head3,{
                                                        FStar_Extraction_ML_Syntax.expr
                                                          =
                                                          FStar_Extraction_ML_Syntax.MLE_Const
                                                          (FStar_Extraction_ML_Syntax.MLC_Unit
                                                          );
                                                        FStar_Extraction_ML_Syntax.mlty
                                                          = uu____7568;
                                                        FStar_Extraction_ML_Syntax.loc
                                                          = uu____7569;_}::[])
                                               ->
                                               FStar_All.pipe_right
                                                 (FStar_Extraction_ML_Syntax.MLE_App
                                                    ((let uu___149_7575 =
                                                        mk_tapp head3
                                                          prefixAsMLTypes
                                                         in
                                                      {
                                                        FStar_Extraction_ML_Syntax.expr
                                                          =
                                                          (uu___149_7575.FStar_Extraction_ML_Syntax.expr);
                                                        FStar_Extraction_ML_Syntax.mlty
                                                          =
                                                          (FStar_Extraction_ML_Syntax.MLTY_Fun
                                                             (FStar_Extraction_ML_Syntax.ml_unit_ty,
                                                               FStar_Extraction_ML_Syntax.E_PURE,
                                                               t2));
                                                        FStar_Extraction_ML_Syntax.loc
                                                          =
                                                          (uu___149_7575.FStar_Extraction_ML_Syntax.loc)
                                                      }),
                                                      [FStar_Extraction_ML_Syntax.ml_unit]))
                                                 (FStar_Extraction_ML_Syntax.with_ty
                                                    t2)
                                           | uu____7576 ->
                                               failwith
                                                 "Impossible: Unexpected head term"
                                            in
                                         (head3, t2, rest))
                                  else err_uninst g head2 (vars, t1) top
                               in
                            (match uu____7379 with
                             | (head_ml1,head_t,args1) ->
                                 (match args1 with
                                  | [] ->
                                      let uu____7637 =
                                        maybe_eta_data_and_project_record g
                                          qual head_t head_ml1
                                         in
                                      (uu____7637,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        head_t)
                                  | uu____7638 ->
                                      extract_app_maybe_projector qual
                                        head_ml1
                                        (FStar_Extraction_ML_Syntax.E_PURE,
                                          head_t) args1)))
                   | FStar_Syntax_Syntax.Tm_fvar uu____7647 ->
                       let uu____7648 =
                         let uu____7661 =
                           FStar_Extraction_ML_UEnv.lookup_term g head2  in
                         match uu____7661 with
                         | (FStar_Util.Inr (uu____7680,x1,x2,x3),q) ->
                             ((x1, x2, x3), q)
                         | uu____7725 -> failwith "FIXME Ty"  in
                       (match uu____7648 with
                        | ((head_ml,(vars,t1),inst_ok),qual) ->
                            let has_typ_apps =
                              match args with
                              | (a,uu____7775)::uu____7776 -> is_type g a
                              | uu____7795 -> false  in
                            let uu____7804 =
                              match vars with
                              | uu____7833::uu____7834 when
                                  (Prims.op_Negation has_typ_apps) && inst_ok
                                  -> (head_ml, t1, args)
                              | uu____7845 ->
                                  let n1 = FStar_List.length vars  in
                                  if n1 <= (FStar_List.length args)
                                  then
                                    let uu____7873 =
                                      FStar_Util.first_N n1 args  in
                                    (match uu____7873 with
                                     | (prefix1,rest) ->
                                         let prefixAsMLTypes =
                                           FStar_List.map
                                             (fun uu____7962  ->
                                                match uu____7962 with
                                                | (x,uu____7968) ->
                                                    term_as_mlty g x) prefix1
                                            in
                                         let t2 =
                                           instantiate (vars, t1)
                                             prefixAsMLTypes
                                            in
                                         let mk_tapp e ty_args =
                                           match ty_args with
                                           | [] -> e
                                           | uu____7981 ->
                                               let uu___147_7984 = e  in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (FStar_Extraction_ML_Syntax.MLE_TApp
                                                      (e, ty_args));
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   =
                                                   (uu___147_7984.FStar_Extraction_ML_Syntax.mlty);
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___147_7984.FStar_Extraction_ML_Syntax.loc)
                                               }
                                            in
                                         let head3 =
                                           match head_ml.FStar_Extraction_ML_Syntax.expr
                                           with
                                           | FStar_Extraction_ML_Syntax.MLE_Name
                                               uu____7988 ->
                                               let uu___148_7989 =
                                                 mk_tapp head_ml
                                                   prefixAsMLTypes
                                                  in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (uu___148_7989.FStar_Extraction_ML_Syntax.expr);
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   = t2;
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___148_7989.FStar_Extraction_ML_Syntax.loc)
                                               }
                                           | FStar_Extraction_ML_Syntax.MLE_Var
                                               uu____7990 ->
                                               let uu___148_7991 =
                                                 mk_tapp head_ml
                                                   prefixAsMLTypes
                                                  in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (uu___148_7991.FStar_Extraction_ML_Syntax.expr);
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   = t2;
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___148_7991.FStar_Extraction_ML_Syntax.loc)
                                               }
                                           | FStar_Extraction_ML_Syntax.MLE_App
                                               (head3,{
                                                        FStar_Extraction_ML_Syntax.expr
                                                          =
                                                          FStar_Extraction_ML_Syntax.MLE_Const
                                                          (FStar_Extraction_ML_Syntax.MLC_Unit
                                                          );
                                                        FStar_Extraction_ML_Syntax.mlty
                                                          = uu____7993;
                                                        FStar_Extraction_ML_Syntax.loc
                                                          = uu____7994;_}::[])
                                               ->
                                               FStar_All.pipe_right
                                                 (FStar_Extraction_ML_Syntax.MLE_App
                                                    ((let uu___149_8000 =
                                                        mk_tapp head3
                                                          prefixAsMLTypes
                                                         in
                                                      {
                                                        FStar_Extraction_ML_Syntax.expr
                                                          =
                                                          (uu___149_8000.FStar_Extraction_ML_Syntax.expr);
                                                        FStar_Extraction_ML_Syntax.mlty
                                                          =
                                                          (FStar_Extraction_ML_Syntax.MLTY_Fun
                                                             (FStar_Extraction_ML_Syntax.ml_unit_ty,
                                                               FStar_Extraction_ML_Syntax.E_PURE,
                                                               t2));
                                                        FStar_Extraction_ML_Syntax.loc
                                                          =
                                                          (uu___149_8000.FStar_Extraction_ML_Syntax.loc)
                                                      }),
                                                      [FStar_Extraction_ML_Syntax.ml_unit]))
                                                 (FStar_Extraction_ML_Syntax.with_ty
                                                    t2)
                                           | uu____8001 ->
                                               failwith
                                                 "Impossible: Unexpected head term"
                                            in
                                         (head3, t2, rest))
                                  else err_uninst g head2 (vars, t1) top
                               in
                            (match uu____7804 with
                             | (head_ml1,head_t,args1) ->
                                 (match args1 with
                                  | [] ->
                                      let uu____8062 =
                                        maybe_eta_data_and_project_record g
                                          qual head_t head_ml1
                                         in
                                      (uu____8062,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        head_t)
                                  | uu____8063 ->
                                      extract_app_maybe_projector qual
                                        head_ml1
                                        (FStar_Extraction_ML_Syntax.E_PURE,
                                          head_t) args1)))
                   | uu____8072 ->
                       let uu____8073 = term_as_mlexpr g head2  in
                       (match uu____8073 with
                        | (head3,f,t1) ->
                            extract_app_maybe_projector
                              FStar_Pervasives_Native.None head3 (f, t1) args)))
       | FStar_Syntax_Syntax.Tm_ascribed (e0,(tc,uu____8091),f) ->
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
           let uu____8158 = check_term_as_mlexpr g e0 f1 t1  in
           (match uu____8158 with | (e,t2) -> (e, f1, t2))
       | FStar_Syntax_Syntax.Tm_let ((is_rec,lbs),e') ->
           let top_level = FStar_Syntax_Syntax.is_top_level lbs  in
           let uu____8189 =
             if is_rec
             then FStar_Syntax_Subst.open_let_rec lbs e'
             else
               (let uu____8203 = FStar_Syntax_Syntax.is_top_level lbs  in
                if uu____8203
                then (lbs, e')
                else
                  (let lb = FStar_List.hd lbs  in
                   let x =
                     let uu____8217 =
                       FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                     FStar_Syntax_Syntax.freshen_bv uu____8217  in
                   let lb1 =
                     let uu___150_8219 = lb  in
                     {
                       FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                       FStar_Syntax_Syntax.lbunivs =
                         (uu___150_8219.FStar_Syntax_Syntax.lbunivs);
                       FStar_Syntax_Syntax.lbtyp =
                         (uu___150_8219.FStar_Syntax_Syntax.lbtyp);
                       FStar_Syntax_Syntax.lbeff =
                         (uu___150_8219.FStar_Syntax_Syntax.lbeff);
                       FStar_Syntax_Syntax.lbdef =
                         (uu___150_8219.FStar_Syntax_Syntax.lbdef)
                     }  in
                   let e'1 =
                     FStar_Syntax_Subst.subst
                       [FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x)] e'
                      in
                   ([lb1], e'1)))
              in
           (match uu____8189 with
            | (lbs1,e'1) ->
                let lbs2 =
                  if top_level
                  then
                    FStar_All.pipe_right lbs1
                      (FStar_List.map
                         (fun lb  ->
                            let tcenv =
                              let uu____8251 =
                                FStar_Ident.lid_of_path
                                  (FStar_List.append
                                     (FStar_Pervasives_Native.fst
                                        g.FStar_Extraction_ML_UEnv.currentModule)
                                     [FStar_Pervasives_Native.snd
                                        g.FStar_Extraction_ML_UEnv.currentModule])
                                  FStar_Range.dummyRange
                                 in
                              FStar_TypeChecker_Env.set_current_module
                                g.FStar_Extraction_ML_UEnv.tcenv uu____8251
                               in
                            FStar_Extraction_ML_UEnv.debug g
                              (fun uu____8258  ->
                                 FStar_Options.set_option "debug_level"
                                   (FStar_Options.List
                                      [FStar_Options.String "Norm";
                                      FStar_Options.String "Extraction"]));
                            (let lbdef =
                               let uu____8262 = FStar_Options.ml_ish ()  in
                               if uu____8262
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
                             let uu___151_8266 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___151_8266.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___151_8266.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___151_8266.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___151_8266.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef
                             })))
                  else lbs1  in
                let maybe_generalize uu____8289 =
                  match uu____8289 with
                  | { FStar_Syntax_Syntax.lbname = lbname_;
                      FStar_Syntax_Syntax.lbunivs = uu____8309;
                      FStar_Syntax_Syntax.lbtyp = t1;
                      FStar_Syntax_Syntax.lbeff = lbeff;
                      FStar_Syntax_Syntax.lbdef = e;_} ->
                      let f_e = effect_as_etag g lbeff  in
                      let t2 = FStar_Syntax_Subst.compress t1  in
                      (match t2.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                           let uu____8379 = FStar_List.hd bs  in
                           FStar_All.pipe_right uu____8379 (is_type_binder g)
                           ->
                           let uu____8392 = FStar_Syntax_Subst.open_comp bs c
                              in
                           (match uu____8392 with
                            | (bs1,c1) ->
                                let uu____8417 =
                                  let uu____8424 =
                                    FStar_Util.prefix_until
                                      (fun x  ->
                                         let uu____8460 = is_type_binder g x
                                            in
                                         Prims.op_Negation uu____8460) bs1
                                     in
                                  match uu____8424 with
                                  | FStar_Pervasives_Native.None  ->
                                      (bs1,
                                        (FStar_Syntax_Util.comp_result c1))
                                  | FStar_Pervasives_Native.Some (bs2,b,rest)
                                      ->
                                      let uu____8548 =
                                        FStar_Syntax_Util.arrow (b :: rest)
                                          c1
                                         in
                                      (bs2, uu____8548)
                                   in
                                (match uu____8417 with
                                 | (tbinders,tbody) ->
                                     let n_tbinders =
                                       FStar_List.length tbinders  in
                                     let e1 =
                                       let uu____8593 = normalize_abs e  in
                                       FStar_All.pipe_right uu____8593
                                         FStar_Syntax_Util.unmeta
                                        in
                                     (match e1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Tm_abs
                                          (bs2,body,copt) ->
                                          let uu____8635 =
                                            FStar_Syntax_Subst.open_term bs2
                                              body
                                             in
                                          (match uu____8635 with
                                           | (bs3,body1) ->
                                               if
                                                 n_tbinders <=
                                                   (FStar_List.length bs3)
                                               then
                                                 let uu____8688 =
                                                   FStar_Util.first_N
                                                     n_tbinders bs3
                                                    in
                                                 (match uu____8688 with
                                                  | (targs,rest_args) ->
                                                      let expected_source_ty
                                                        =
                                                        let s =
                                                          FStar_List.map2
                                                            (fun uu____8776 
                                                               ->
                                                               fun uu____8777
                                                                  ->
                                                                 match 
                                                                   (uu____8776,
                                                                    uu____8777)
                                                                 with
                                                                 | ((x,uu____8795),
                                                                    (y,uu____8797))
                                                                    ->
                                                                    let uu____8806
                                                                    =
                                                                    let uu____8813
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    y  in
                                                                    (x,
                                                                    uu____8813)
                                                                     in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____8806)
                                                            tbinders targs
                                                           in
                                                        FStar_Syntax_Subst.subst
                                                          s tbody
                                                         in
                                                      let env =
                                                        FStar_List.fold_left
                                                          (fun env  ->
                                                             fun uu____8824 
                                                               ->
                                                               match uu____8824
                                                               with
                                                               | (a,uu____8830)
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
                                                        let uu____8843 =
                                                          FStar_All.pipe_right
                                                            targs
                                                            (FStar_List.map
                                                               (fun
                                                                  uu____8873 
                                                                  ->
                                                                  match uu____8873
                                                                  with
                                                                  | (x,uu____8883)
                                                                    ->
                                                                    FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                                    x))
                                                           in
                                                        (uu____8843,
                                                          expected_t)
                                                         in
                                                      let add_unit =
                                                        match rest_args with
                                                        | [] ->
                                                            let uu____8895 =
                                                              is_fstar_value
                                                                body1
                                                               in
                                                            Prims.op_Negation
                                                              uu____8895
                                                        | uu____8896 -> false
                                                         in
                                                      let rest_args1 =
                                                        if add_unit
                                                        then unit_binder ::
                                                          rest_args
                                                        else rest_args  in
                                                      let polytype1 =
                                                        if add_unit
                                                        then
                                                          FStar_Extraction_ML_Syntax.push_unit
                                                            polytype
                                                        else polytype  in
                                                      let body2 =
                                                        FStar_Syntax_Util.abs
                                                          rest_args1 body1
                                                          copt
                                                         in
                                                      (lbname_, f_e,
                                                        (t2,
                                                          (targs, polytype1)),
                                                        add_unit, body2))
                                               else
                                                 failwith
                                                   "Not enough type binders")
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          uu____8965 ->
                                          let env =
                                            FStar_List.fold_left
                                              (fun env  ->
                                                 fun uu____8982  ->
                                                   match uu____8982 with
                                                   | (a,uu____8988) ->
                                                       FStar_Extraction_ML_UEnv.extend_ty
                                                         env a
                                                         FStar_Pervasives_Native.None)
                                              g tbinders
                                             in
                                          let expected_t =
                                            term_as_mlty env tbody  in
                                          let polytype =
                                            let uu____9001 =
                                              FStar_All.pipe_right tbinders
                                                (FStar_List.map
                                                   (fun uu____9025  ->
                                                      match uu____9025 with
                                                      | (x,uu____9035) ->
                                                          FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                            x))
                                               in
                                            (uu____9001, expected_t)  in
                                          let args =
                                            FStar_All.pipe_right tbinders
                                              (FStar_List.map
                                                 (fun uu____9055  ->
                                                    match uu____9055 with
                                                    | (bv,uu____9061) ->
                                                        let uu____9062 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            bv
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____9062
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
                                          uu____9116 ->
                                          let env =
                                            FStar_List.fold_left
                                              (fun env  ->
                                                 fun uu____9127  ->
                                                   match uu____9127 with
                                                   | (a,uu____9133) ->
                                                       FStar_Extraction_ML_UEnv.extend_ty
                                                         env a
                                                         FStar_Pervasives_Native.None)
                                              g tbinders
                                             in
                                          let expected_t =
                                            term_as_mlty env tbody  in
                                          let polytype =
                                            let uu____9146 =
                                              FStar_All.pipe_right tbinders
                                                (FStar_List.map
                                                   (fun uu____9170  ->
                                                      match uu____9170 with
                                                      | (x,uu____9180) ->
                                                          FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                            x))
                                               in
                                            (uu____9146, expected_t)  in
                                          let args =
                                            FStar_All.pipe_right tbinders
                                              (FStar_List.map
                                                 (fun uu____9200  ->
                                                    match uu____9200 with
                                                    | (bv,uu____9206) ->
                                                        let uu____9207 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            bv
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____9207
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
                                          uu____9261 ->
                                          let env =
                                            FStar_List.fold_left
                                              (fun env  ->
                                                 fun uu____9272  ->
                                                   match uu____9272 with
                                                   | (a,uu____9278) ->
                                                       FStar_Extraction_ML_UEnv.extend_ty
                                                         env a
                                                         FStar_Pervasives_Native.None)
                                              g tbinders
                                             in
                                          let expected_t =
                                            term_as_mlty env tbody  in
                                          let polytype =
                                            let uu____9291 =
                                              FStar_All.pipe_right tbinders
                                                (FStar_List.map
                                                   (fun uu____9315  ->
                                                      match uu____9315 with
                                                      | (x,uu____9325) ->
                                                          FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                            x))
                                               in
                                            (uu____9291, expected_t)  in
                                          let args =
                                            FStar_All.pipe_right tbinders
                                              (FStar_List.map
                                                 (fun uu____9345  ->
                                                    match uu____9345 with
                                                    | (bv,uu____9351) ->
                                                        let uu____9352 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            bv
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____9352
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
                                      | uu____9406 ->
                                          err_value_restriction e1)))
                       | uu____9425 ->
                           let expected_t = term_as_mlty g t2  in
                           (lbname_, f_e, (t2, ([], ([], expected_t))),
                             false, e))
                   in
                let check_lb env uu____9529 =
                  match uu____9529 with
                  | (nm,(lbname,f,(t1,(targs,polytype)),add_unit,e)) ->
                      let env1 =
                        FStar_List.fold_left
                          (fun env1  ->
                             fun uu____9664  ->
                               match uu____9664 with
                               | (a,uu____9670) ->
                                   FStar_Extraction_ML_UEnv.extend_ty env1 a
                                     FStar_Pervasives_Native.None) env targs
                         in
                      let expected_t = FStar_Pervasives_Native.snd polytype
                         in
                      let uu____9672 =
                        check_term_as_mlexpr env1 e f expected_t  in
                      (match uu____9672 with
                       | (e1,uu____9682) ->
                           let f1 = maybe_downgrade_eff env1 f expected_t  in
                           (f1,
                             {
                               FStar_Extraction_ML_Syntax.mllb_name = nm;
                               FStar_Extraction_ML_Syntax.mllb_tysc =
                                 (FStar_Pervasives_Native.Some polytype);
                               FStar_Extraction_ML_Syntax.mllb_add_unit =
                                 add_unit;
                               FStar_Extraction_ML_Syntax.mllb_def = e1;
                               FStar_Extraction_ML_Syntax.print_typ = true
                             }))
                   in
                let lbs3 =
                  FStar_All.pipe_right lbs2 (FStar_List.map maybe_generalize)
                   in
                let uu____9749 =
                  FStar_List.fold_right
                    (fun lb  ->
                       fun uu____9840  ->
                         match uu____9840 with
                         | (env,lbs4) ->
                             let uu____9965 = lb  in
                             (match uu____9965 with
                              | (lbname,uu____10013,(t1,(uu____10015,polytype)),add_unit,uu____10018)
                                  ->
                                  let uu____10031 =
                                    FStar_Extraction_ML_UEnv.extend_lb env
                                      lbname t1 polytype add_unit true
                                     in
                                  (match uu____10031 with
                                   | (env1,nm) -> (env1, ((nm, lb) :: lbs4)))))
                    lbs3 (g, [])
                   in
                (match uu____9749 with
                 | (env_body,lbs4) ->
                     let env_def = if is_rec then env_body else g  in
                     let lbs5 =
                       FStar_All.pipe_right lbs4
                         (FStar_List.map (check_lb env_def))
                        in
                     let e'_rng = e'1.FStar_Syntax_Syntax.pos  in
                     let uu____10308 = term_as_mlexpr env_body e'1  in
                     (match uu____10308 with
                      | (e'2,f',t') ->
                          let f =
                            let uu____10325 =
                              let uu____10328 =
                                FStar_List.map FStar_Pervasives_Native.fst
                                  lbs5
                                 in
                              f' :: uu____10328  in
                            FStar_Extraction_ML_Util.join_l e'_rng
                              uu____10325
                             in
                          let is_rec1 =
                            if is_rec = true
                            then FStar_Extraction_ML_Syntax.Rec
                            else FStar_Extraction_ML_Syntax.NonRec  in
                          let uu____10337 =
                            let uu____10338 =
                              let uu____10339 =
                                let uu____10340 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    lbs5
                                   in
                                (is_rec1, [], uu____10340)  in
                              mk_MLE_Let top_level uu____10339 e'2  in
                            let uu____10351 =
                              FStar_Extraction_ML_Util.mlloc_of_range
                                t.FStar_Syntax_Syntax.pos
                               in
                            FStar_Extraction_ML_Syntax.with_ty_loc t'
                              uu____10338 uu____10351
                             in
                          (uu____10337, f, t'))))
       | FStar_Syntax_Syntax.Tm_match (scrutinee,pats) ->
           let uu____10390 = term_as_mlexpr g scrutinee  in
           (match uu____10390 with
            | (e,f_e,t_e) ->
                let uu____10406 = check_pats_for_ite pats  in
                (match uu____10406 with
                 | (b,then_e,else_e) ->
                     let no_lift x t1 = x  in
                     if b
                     then
                       (match (then_e, else_e) with
                        | (FStar_Pervasives_Native.Some
                           then_e1,FStar_Pervasives_Native.Some else_e1) ->
                            let uu____10463 = term_as_mlexpr g then_e1  in
                            (match uu____10463 with
                             | (then_mle,f_then,t_then) ->
                                 let uu____10479 = term_as_mlexpr g else_e1
                                    in
                                 (match uu____10479 with
                                  | (else_mle,f_else,t_else) ->
                                      let uu____10495 =
                                        let uu____10504 =
                                          type_leq g t_then t_else  in
                                        if uu____10504
                                        then (t_else, no_lift)
                                        else
                                          (let uu____10518 =
                                             type_leq g t_else t_then  in
                                           if uu____10518
                                           then (t_then, no_lift)
                                           else
                                             (FStar_Extraction_ML_Syntax.MLTY_Top,
                                               FStar_Extraction_ML_Syntax.apply_obj_repr))
                                         in
                                      (match uu____10495 with
                                       | (t_branch,maybe_lift1) ->
                                           let uu____10552 =
                                             let uu____10553 =
                                               let uu____10554 =
                                                 let uu____10563 =
                                                   maybe_lift1 then_mle
                                                     t_then
                                                    in
                                                 let uu____10564 =
                                                   let uu____10567 =
                                                     maybe_lift1 else_mle
                                                       t_else
                                                      in
                                                   FStar_Pervasives_Native.Some
                                                     uu____10567
                                                    in
                                                 (e, uu____10563,
                                                   uu____10564)
                                                  in
                                               FStar_Extraction_ML_Syntax.MLE_If
                                                 uu____10554
                                                in
                                             FStar_All.pipe_left
                                               (FStar_Extraction_ML_Syntax.with_ty
                                                  t_branch) uu____10553
                                              in
                                           let uu____10570 =
                                             FStar_Extraction_ML_Util.join
                                               then_e1.FStar_Syntax_Syntax.pos
                                               f_then f_else
                                              in
                                           (uu____10552, uu____10570,
                                             t_branch))))
                        | uu____10571 ->
                            failwith
                              "ITE pats matched but then and else expressions not found?")
                     else
                       (let uu____10587 =
                          FStar_All.pipe_right pats
                            (FStar_Util.fold_map
                               (fun compat  ->
                                  fun br  ->
                                    let uu____10696 =
                                      FStar_Syntax_Subst.open_branch br  in
                                    match uu____10696 with
                                    | (pat,when_opt,branch1) ->
                                        let uu____10740 =
                                          extract_pat g pat t_e  in
                                        (match uu____10740 with
                                         | (env,p,pat_t_compat) ->
                                             let uu____10798 =
                                               match when_opt with
                                               | FStar_Pervasives_Native.None
                                                    ->
                                                   (FStar_Pervasives_Native.None,
                                                     FStar_Extraction_ML_Syntax.E_PURE)
                                               | FStar_Pervasives_Native.Some
                                                   w ->
                                                   let uu____10820 =
                                                     term_as_mlexpr env w  in
                                                   (match uu____10820 with
                                                    | (w1,f_w,t_w) ->
                                                        let w2 =
                                                          maybe_coerce env w1
                                                            t_w
                                                            FStar_Extraction_ML_Syntax.ml_bool_ty
                                                           in
                                                        ((FStar_Pervasives_Native.Some
                                                            w2), f_w))
                                                in
                                             (match uu____10798 with
                                              | (when_opt1,f_when) ->
                                                  let uu____10869 =
                                                    term_as_mlexpr env
                                                      branch1
                                                     in
                                                  (match uu____10869 with
                                                   | (mlbranch,f_branch,t_branch)
                                                       ->
                                                       let uu____10903 =
                                                         FStar_All.pipe_right
                                                           p
                                                           (FStar_List.map
                                                              (fun
                                                                 uu____10980 
                                                                 ->
                                                                 match uu____10980
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
                                                         uu____10903)))))
                               true)
                           in
                        match uu____10587 with
                        | (pat_t_compat,mlbranches) ->
                            let mlbranches1 = FStar_List.flatten mlbranches
                               in
                            let e1 =
                              if pat_t_compat
                              then e
                              else
                                (FStar_Extraction_ML_UEnv.debug g
                                   (fun uu____11145  ->
                                      let uu____11146 =
                                        FStar_Extraction_ML_Code.string_of_mlexpr
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          e
                                         in
                                      let uu____11147 =
                                        FStar_Extraction_ML_Code.string_of_mlty
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          t_e
                                         in
                                      FStar_Util.print2
                                        "Coercing scrutinee %s from type %s because pattern type is incompatible\n"
                                        uu____11146 uu____11147);
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty t_e)
                                   (FStar_Extraction_ML_Syntax.MLE_Coerce
                                      (e, t_e,
                                        FStar_Extraction_ML_Syntax.MLTY_Top)))
                               in
                            (match mlbranches1 with
                             | [] ->
                                 let uu____11172 =
                                   let uu____11181 =
                                     let uu____11198 =
                                       FStar_Syntax_Syntax.lid_as_fv
                                         FStar_Parser_Const.failwith_lid
                                         FStar_Syntax_Syntax.Delta_constant
                                         FStar_Pervasives_Native.None
                                        in
                                     FStar_Extraction_ML_UEnv.lookup_fv g
                                       uu____11198
                                      in
                                   FStar_All.pipe_left FStar_Util.right
                                     uu____11181
                                    in
                                 (match uu____11172 with
                                  | (uu____11241,fw,uu____11243,uu____11244)
                                      ->
                                      let uu____11245 =
                                        let uu____11246 =
                                          let uu____11247 =
                                            let uu____11254 =
                                              let uu____11257 =
                                                FStar_All.pipe_left
                                                  (FStar_Extraction_ML_Syntax.with_ty
                                                     FStar_Extraction_ML_Syntax.ml_string_ty)
                                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                                     (FStar_Extraction_ML_Syntax.MLC_String
                                                        "unreachable"))
                                                 in
                                              [uu____11257]  in
                                            (fw, uu____11254)  in
                                          FStar_Extraction_ML_Syntax.MLE_App
                                            uu____11247
                                           in
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             FStar_Extraction_ML_Syntax.ml_unit_ty)
                                          uu____11246
                                         in
                                      (uu____11245,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        FStar_Extraction_ML_Syntax.ml_unit_ty))
                             | (uu____11260,uu____11261,(uu____11262,f_first,t_first))::rest
                                 ->
                                 let uu____11322 =
                                   FStar_List.fold_left
                                     (fun uu____11364  ->
                                        fun uu____11365  ->
                                          match (uu____11364, uu____11365)
                                          with
                                          | ((topt,f),(uu____11422,uu____11423,
                                                       (uu____11424,f_branch,t_branch)))
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
                                                    let uu____11480 =
                                                      type_leq g t1 t_branch
                                                       in
                                                    if uu____11480
                                                    then
                                                      FStar_Pervasives_Native.Some
                                                        t_branch
                                                    else
                                                      (let uu____11484 =
                                                         type_leq g t_branch
                                                           t1
                                                          in
                                                       if uu____11484
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
                                 (match uu____11322 with
                                  | (topt,f_match) ->
                                      let mlbranches2 =
                                        FStar_All.pipe_right mlbranches1
                                          (FStar_List.map
                                             (fun uu____11579  ->
                                                match uu____11579 with
                                                | (p,(wopt,uu____11608),
                                                   (b1,uu____11610,t1)) ->
                                                    let b2 =
                                                      match topt with
                                                      | FStar_Pervasives_Native.None
                                                           ->
                                                          FStar_Extraction_ML_Syntax.apply_obj_repr
                                                            b1 t1
                                                      | FStar_Pervasives_Native.Some
                                                          uu____11629 -> b1
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
                                      let uu____11634 =
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             t_match)
                                          (FStar_Extraction_ML_Syntax.MLE_Match
<<<<<<< HEAD
                                             (e1, mlbranches2))
                                         in
                                      (uu____11634, f_match, t_match)))))))

let ind_discriminator_body :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlmodule1
  =
=======
                                             (e1, mlbranches2)) in
                                      (uu____11465, f_match, t_match)))))))
let (ind_discriminator_body
  :FStar_Extraction_ML_UEnv.env ->
     FStar_Ident.lident ->
       FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlmodule1)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun env  ->
    fun discName  ->
      fun constrName  ->
        let uu____11657 =
          let uu____11662 =
            FStar_TypeChecker_Env.lookup_lid
              env.FStar_Extraction_ML_UEnv.tcenv discName
             in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____11662  in
        match uu____11657 with
        | (uu____11687,fstar_disc_type) ->
            let wildcards =
              let uu____11700 =
                let uu____11701 = FStar_Syntax_Subst.compress fstar_disc_type
                   in
                uu____11701.FStar_Syntax_Syntax.n  in
              match uu____11700 with
              | FStar_Syntax_Syntax.Tm_arrow (binders,uu____11715) ->
                  let uu____11732 =
                    FStar_All.pipe_right binders
                      (FStar_List.filter
                         (fun uu___144_11764  ->
                            match uu___144_11764 with
                            | (uu____11771,FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____11772)) ->
                                true
                            | uu____11775 -> false))
                     in
                  FStar_All.pipe_right uu____11732
                    (FStar_List.map
                       (fun uu____11816  ->
                          let uu____11823 = fresh "_"  in
                          (uu____11823, FStar_Extraction_ML_Syntax.MLTY_Top)))
              | uu____11832 -> failwith "Discriminator must be a function"
               in
            let mlid = fresh "_discr_"  in
            let targ = FStar_Extraction_ML_Syntax.MLTY_Top  in
            let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top  in
            let discrBody =
              let uu____11851 =
                let uu____11852 =
                  let uu____11863 =
                    let uu____11864 =
                      let uu____11865 =
                        let uu____11880 =
                          let uu____11881 =
                            let uu____11882 =
                              let uu____11883 =
                                FStar_Extraction_ML_Syntax.idsym mlid  in
                              ([], uu____11883)  in
                            FStar_Extraction_ML_Syntax.MLE_Name uu____11882
                             in
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty targ)
                            uu____11881
                           in
                        let uu____11886 =
                          let uu____11897 =
                            let uu____11906 =
                              let uu____11907 =
                                let uu____11914 =
                                  FStar_Extraction_ML_Syntax.mlpath_of_lident
                                    constrName
                                   in
                                (uu____11914,
                                  [FStar_Extraction_ML_Syntax.MLP_Wild])
                                 in
                              FStar_Extraction_ML_Syntax.MLP_CTor uu____11907
                               in
                            let uu____11917 =
                              FStar_All.pipe_left
                                (FStar_Extraction_ML_Syntax.with_ty
                                   FStar_Extraction_ML_Syntax.ml_bool_ty)
                                (FStar_Extraction_ML_Syntax.MLE_Const
                                   (FStar_Extraction_ML_Syntax.MLC_Bool true))
                               in
                            (uu____11906, FStar_Pervasives_Native.None,
                              uu____11917)
                             in
                          let uu____11920 =
                            let uu____11931 =
                              let uu____11940 =
                                FStar_All.pipe_left
                                  (FStar_Extraction_ML_Syntax.with_ty
                                     FStar_Extraction_ML_Syntax.ml_bool_ty)
                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                     (FStar_Extraction_ML_Syntax.MLC_Bool
                                        false))
                                 in
                              (FStar_Extraction_ML_Syntax.MLP_Wild,
                                FStar_Pervasives_Native.None, uu____11940)
                               in
                            [uu____11931]  in
                          uu____11897 :: uu____11920  in
                        (uu____11880, uu____11886)  in
                      FStar_Extraction_ML_Syntax.MLE_Match uu____11865  in
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.ml_bool_ty) uu____11864
                     in
                  ((FStar_List.append wildcards [(mlid, targ)]), uu____11863)
                   in
                FStar_Extraction_ML_Syntax.MLE_Fun uu____11852  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty disc_ty) uu____11851
               in
            let uu____12015 =
              let uu____12016 =
                let uu____12019 =
                  let uu____12020 =
                    FStar_Extraction_ML_UEnv.convIdent
                      discName.FStar_Ident.ident
                     in
                  {
                    FStar_Extraction_ML_Syntax.mllb_name = uu____12020;
                    FStar_Extraction_ML_Syntax.mllb_tysc =
                      FStar_Pervasives_Native.None;
                    FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                    FStar_Extraction_ML_Syntax.mllb_def = discrBody;
                    FStar_Extraction_ML_Syntax.print_typ = false
                  }  in
                [uu____12019]  in
              (FStar_Extraction_ML_Syntax.NonRec, [], uu____12016)  in
            FStar_Extraction_ML_Syntax.MLM_Let uu____12015
  