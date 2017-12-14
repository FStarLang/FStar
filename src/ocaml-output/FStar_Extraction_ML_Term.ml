open Prims
exception Un_extractable 
let uu___is_Un_extractable : Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Un_extractable  -> true | uu____4 -> false
  
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
  'Auu____50 .
    FStar_Ident.ident Prims.list ->
      'Auu____50 Prims.list ->
        (Prims.string,'Auu____50) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun fs  ->
    fun vs  ->
      FStar_List.map2 (fun f  -> fun e  -> ((f.FStar_Ident.idText), e)) fs vs
  
let fail :
  'Auu____84 .
    FStar_Range.range ->
      (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2 ->
        'Auu____84
  = fun r  -> fun err  -> FStar_Errors.raise_error err r 
let err_uninst :
  'Auu____106 .
    FStar_Extraction_ML_UEnv.env ->
      FStar_Syntax_Syntax.term ->
        (Prims.string Prims.list,FStar_Extraction_ML_Syntax.mlty)
          FStar_Pervasives_Native.tuple2 ->
          FStar_Syntax_Syntax.term -> 'Auu____106
  =
  fun env  ->
    fun t  ->
      fun uu____127  ->
        fun app  ->
          match uu____127 with
          | (vars,ty) ->
              let uu____141 =
                let uu____146 =
                  let uu____147 = FStar_Syntax_Print.term_to_string t  in
                  let uu____148 =
                    FStar_All.pipe_right vars (FStar_String.concat ", ")  in
                  let uu____151 =
                    FStar_Extraction_ML_Code.string_of_mlty
                      env.FStar_Extraction_ML_UEnv.currentModule ty
                     in
                  let uu____152 = FStar_Syntax_Print.term_to_string app  in
                  FStar_Util.format4
                    "Variable %s has a polymorphic type (forall %s. %s); expected it to be fully instantiated, but got %s"
                    uu____147 uu____148 uu____151 uu____152
                   in
                (FStar_Errors.Fatal_Uninstantiated, uu____146)  in
              fail t.FStar_Syntax_Syntax.pos uu____141
  
let err_ill_typed_application :
  'Auu____159 'Auu____160 .
    FStar_Extraction_ML_UEnv.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term,'Auu____160) FStar_Pervasives_Native.tuple2
          Prims.list -> FStar_Extraction_ML_Syntax.mlty -> 'Auu____159
  =
  fun env  ->
    fun t  ->
      fun args  ->
        fun ty  ->
          let uu____189 =
            let uu____194 =
              let uu____195 = FStar_Syntax_Print.term_to_string t  in
              let uu____196 =
                let uu____197 =
                  FStar_All.pipe_right args
                    (FStar_List.map
                       (fun uu____215  ->
                          match uu____215 with
                          | (x,uu____221) ->
                              FStar_Syntax_Print.term_to_string x))
                   in
                FStar_All.pipe_right uu____197 (FStar_String.concat " ")  in
              let uu____224 =
                FStar_Extraction_ML_Code.string_of_mlty
                  env.FStar_Extraction_ML_UEnv.currentModule ty
                 in
              FStar_Util.format3
                "Ill-typed application: application is %s \n remaining args are %s\nml type of head is %s\n"
                uu____195 uu____196 uu____224
               in
            (FStar_Errors.Fatal_IllTyped, uu____194)  in
          fail t.FStar_Syntax_Syntax.pos uu____189
  
let err_value_restriction :
  'Auu____227 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> 'Auu____227
  =
  fun t  ->
    let uu____236 =
      let uu____241 =
        let uu____242 = FStar_Syntax_Print.tag_of_term t  in
        let uu____243 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format2
          "Refusing to generalize because of the value restriction: (%s) %s"
          uu____242 uu____243
         in
      (FStar_Errors.Fatal_ValueRestriction, uu____241)  in
    fail t.FStar_Syntax_Syntax.pos uu____236
  
let err_unexpected_eff :
  'Auu____248 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Extraction_ML_Syntax.e_tag ->
        FStar_Extraction_ML_Syntax.e_tag -> 'Auu____248
  =
  fun t  ->
    fun f0  ->
      fun f1  ->
        let uu____265 =
          let uu____270 =
            let uu____271 = FStar_Syntax_Print.term_to_string t  in
            FStar_Util.format3
              "for expression %s, Expected effect %s; got effect %s"
              uu____271 (FStar_Extraction_ML_Util.eff_to_string f0)
              (FStar_Extraction_ML_Util.eff_to_string f1)
             in
          (FStar_Errors.Fatal_UnexpectedEffect, uu____270)  in
        fail t.FStar_Syntax_Syntax.pos uu____265
  
let effect_as_etag :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Ident.lident -> FStar_Extraction_ML_Syntax.e_tag
  =
  let cache = FStar_Util.smap_create (Prims.parse_int "20")  in
  let rec delta_norm_eff g l =
    let uu____286 = FStar_Util.smap_try_find cache l.FStar_Ident.str  in
    match uu____286 with
    | FStar_Pervasives_Native.Some l1 -> l1
    | FStar_Pervasives_Native.None  ->
        let res =
          let uu____291 =
            FStar_TypeChecker_Env.lookup_effect_abbrev
              g.FStar_Extraction_ML_UEnv.tcenv [FStar_Syntax_Syntax.U_zero] l
             in
          match uu____291 with
          | FStar_Pervasives_Native.None  -> l
          | FStar_Pervasives_Native.Some (uu____302,c) ->
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
               let uu____335 =
                 FStar_All.pipe_right qualifiers
                   (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                  in
               if uu____335
               then FStar_Extraction_ML_Syntax.E_PURE
               else FStar_Extraction_ML_Syntax.E_IMPURE
           | FStar_Pervasives_Native.None  ->
               FStar_Extraction_ML_Syntax.E_IMPURE)
  
let rec is_arity :
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t  in
      let uu____352 =
        let uu____353 = FStar_Syntax_Subst.compress t1  in
        uu____353.FStar_Syntax_Syntax.n  in
      match uu____352 with
      | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____356 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_ascribed uu____381 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_meta uu____408 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_uvar uu____415 -> false
      | FStar_Syntax_Syntax.Tm_constant uu____432 -> false
      | FStar_Syntax_Syntax.Tm_name uu____433 -> false
      | FStar_Syntax_Syntax.Tm_bvar uu____434 -> false
      | FStar_Syntax_Syntax.Tm_type uu____435 -> true
      | FStar_Syntax_Syntax.Tm_arrow (uu____436,c) ->
          is_arity env (FStar_Syntax_Util.comp_result c)
      | FStar_Syntax_Syntax.Tm_fvar uu____454 ->
          let t2 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Normalize.AllowUnboundUniverses;
              FStar_TypeChecker_Normalize.EraseUniverses;
              FStar_TypeChecker_Normalize.UnfoldUntil
                FStar_Syntax_Syntax.Delta_constant]
              env.FStar_Extraction_ML_UEnv.tcenv t1
             in
          let uu____456 =
            let uu____457 = FStar_Syntax_Subst.compress t2  in
            uu____457.FStar_Syntax_Syntax.n  in
          (match uu____456 with
           | FStar_Syntax_Syntax.Tm_fvar uu____460 -> false
           | uu____461 -> is_arity env t2)
      | FStar_Syntax_Syntax.Tm_app uu____462 ->
          let uu____477 = FStar_Syntax_Util.head_and_args t1  in
          (match uu____477 with | (head1,uu____493) -> is_arity env head1)
      | FStar_Syntax_Syntax.Tm_uinst (head1,uu____515) -> is_arity env head1
      | FStar_Syntax_Syntax.Tm_refine (x,uu____521) ->
          is_arity env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_abs (uu____526,body,uu____528) ->
          is_arity env body
      | FStar_Syntax_Syntax.Tm_let (uu____549,body) -> is_arity env body
      | FStar_Syntax_Syntax.Tm_match (uu____567,branches) ->
          (match branches with
           | (uu____605,uu____606,e)::uu____608 -> is_arity env e
           | uu____655 -> false)
  
let rec is_type_aux :
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____679 ->
          let uu____704 =
            let uu____705 = FStar_Syntax_Print.tag_of_term t1  in
            FStar_Util.format1 "Impossible: %s" uu____705  in
          failwith uu____704
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____706 =
            let uu____707 = FStar_Syntax_Print.tag_of_term t1  in
            FStar_Util.format1 "Impossible: %s" uu____707  in
          failwith uu____706
      | FStar_Syntax_Syntax.Tm_constant uu____708 -> false
      | FStar_Syntax_Syntax.Tm_type uu____709 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____710 -> true
      | FStar_Syntax_Syntax.Tm_arrow uu____717 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.failwith_lid ->
          false
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Extraction_ML_UEnv.is_type_name env fv
      | FStar_Syntax_Syntax.Tm_uvar (uu____732,t2) -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_bvar
          { FStar_Syntax_Syntax.ppname = uu____758;
            FStar_Syntax_Syntax.index = uu____759;
            FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_name
          { FStar_Syntax_Syntax.ppname = uu____763;
            FStar_Syntax_Syntax.index = uu____764;
            FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____769,uu____770) ->
          is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____812) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____819) ->
          let uu____840 = FStar_Syntax_Subst.open_term bs body  in
          (match uu____840 with | (uu____845,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
          let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
          let uu____862 =
            let uu____867 =
              let uu____868 = FStar_Syntax_Syntax.mk_binder x  in [uu____868]
               in
            FStar_Syntax_Subst.open_term uu____867 body  in
          (match uu____862 with | (uu____869,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_let ((uu____871,lbs),body) ->
          let uu____888 = FStar_Syntax_Subst.open_let_rec lbs body  in
          (match uu____888 with | (uu____895,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_match (uu____901,branches) ->
          (match branches with
           | b::uu____940 ->
               let uu____985 = FStar_Syntax_Subst.open_branch b  in
               (match uu____985 with
                | (uu____986,uu____987,e) -> is_type_aux env e)
           | uu____1005 -> false)
      | FStar_Syntax_Syntax.Tm_meta (t2,uu____1023) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_app (head1,uu____1029) ->
          is_type_aux env head1
  
let is_type :
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      FStar_Extraction_ML_UEnv.debug env
        (fun uu____1060  ->
           let uu____1061 = FStar_Syntax_Print.tag_of_term t  in
           let uu____1062 = FStar_Syntax_Print.term_to_string t  in
           FStar_Util.print2 "checking is_type (%s) %s\n" uu____1061
             uu____1062);
      (let b = is_type_aux env t  in
       FStar_Extraction_ML_UEnv.debug env
         (fun uu____1068  ->
            if b
            then
              let uu____1069 = FStar_Syntax_Print.term_to_string t  in
              let uu____1070 = FStar_Syntax_Print.tag_of_term t  in
              FStar_Util.print2 "is_type %s (%s)\n" uu____1069 uu____1070
            else
              (let uu____1072 = FStar_Syntax_Print.term_to_string t  in
               let uu____1073 = FStar_Syntax_Print.tag_of_term t  in
               FStar_Util.print2 "not a type %s (%s)\n" uu____1072 uu____1073));
       b)
  
let is_type_binder :
  'Auu____1077 .
    FStar_Extraction_ML_UEnv.env ->
      (FStar_Syntax_Syntax.bv,'Auu____1077) FStar_Pervasives_Native.tuple2 ->
        Prims.bool
  =
  fun env  ->
    fun x  ->
      is_arity env (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
  
let is_constructor : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1097 =
      let uu____1098 = FStar_Syntax_Subst.compress t  in
      uu____1098.FStar_Syntax_Syntax.n  in
    match uu____1097 with
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____1101;
          FStar_Syntax_Syntax.fv_delta = uu____1102;
          FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
            (FStar_Syntax_Syntax.Data_ctor );_}
        -> true
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____1103;
          FStar_Syntax_Syntax.fv_delta = uu____1104;
          FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
            (FStar_Syntax_Syntax.Record_ctor uu____1105);_}
        -> true
    | uu____1112 -> false
  
let rec is_fstar_value : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1116 =
      let uu____1117 = FStar_Syntax_Subst.compress t  in
      uu____1117.FStar_Syntax_Syntax.n  in
    match uu____1116 with
    | FStar_Syntax_Syntax.Tm_constant uu____1120 -> true
    | FStar_Syntax_Syntax.Tm_bvar uu____1121 -> true
    | FStar_Syntax_Syntax.Tm_fvar uu____1122 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____1123 -> true
    | FStar_Syntax_Syntax.Tm_app (head1,args) ->
        let uu____1162 = is_constructor head1  in
        if uu____1162
        then
          FStar_All.pipe_right args
            (FStar_List.for_all
               (fun uu____1178  ->
                  match uu____1178 with
                  | (te,uu____1184) -> is_fstar_value te))
        else false
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____1187) -> is_fstar_value t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____1193,uu____1194) ->
        is_fstar_value t1
    | uu____1235 -> false
  
let rec is_ml_value : FStar_Extraction_ML_Syntax.mlexpr -> Prims.bool =
  fun e  ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_Const uu____1239 -> true
    | FStar_Extraction_ML_Syntax.MLE_Var uu____1240 -> true
    | FStar_Extraction_ML_Syntax.MLE_Name uu____1241 -> true
    | FStar_Extraction_ML_Syntax.MLE_Fun uu____1242 -> true
    | FStar_Extraction_ML_Syntax.MLE_CTor (uu____1253,exps) ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Tuple exps ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Record (uu____1262,fields) ->
        FStar_Util.for_all
          (fun uu____1287  ->
             match uu____1287 with | (uu____1292,e1) -> is_ml_value e1)
          fields
    | FStar_Extraction_ML_Syntax.MLE_TApp (h,uu____1295) -> is_ml_value h
    | uu____1300 -> false
  
let fresh : Prims.string -> Prims.string =
  let c = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun x  ->
    FStar_Util.incr c;
    (let uu____1329 =
       let uu____1330 = FStar_ST.op_Bang c  in
       FStar_Util.string_of_int uu____1330  in
     Prims.strcat x uu____1329)
  
let normalize_abs : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t0  ->
    let rec aux bs t copt =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_abs (bs',body,copt1) ->
          aux (FStar_List.append bs bs') body copt1
      | uu____1450 ->
          let e' = FStar_Syntax_Util.unascribe t1  in
          let uu____1452 = FStar_Syntax_Util.is_fun e'  in
          if uu____1452
          then aux bs e' copt
          else FStar_Syntax_Util.abs bs e' copt
       in
    aux [] t0 FStar_Pervasives_Native.None
  
let unit_binder : FStar_Syntax_Syntax.binder =
  let uu____1458 =
    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
      FStar_Syntax_Syntax.t_unit
     in
  FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____1458 
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
      (let uu____1536 = FStar_List.hd l  in
       match uu____1536 with
       | (p1,w1,e1) ->
           let uu____1570 =
             let uu____1579 = FStar_List.tl l  in FStar_List.hd uu____1579
              in
           (match uu____1570 with
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
                 | uu____1653 -> def)))
  
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
            let uu____1710 = erasable g f ty  in
            if uu____1710
            then
              let uu____1711 =
                type_leq g ty FStar_Extraction_ML_Syntax.ml_unit_ty  in
              (if uu____1711
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
      let uu____1720 = FStar_Extraction_ML_Util.doms_and_cod t  in
      match uu____1720 with
      | (ts,r) ->
          if ts = []
          then e
          else
            (let vs = FStar_List.map (fun uu____1740  -> fresh "a") ts  in
             let vs_ts = FStar_List.zip vs ts  in
             let vs_es =
               let uu____1751 = FStar_List.zip vs ts  in
               FStar_List.map
                 (fun uu____1765  ->
                    match uu____1765 with
                    | (v1,t1) ->
                        FStar_Extraction_ML_Syntax.with_ty t1
                          (FStar_Extraction_ML_Syntax.MLE_Var v1)) uu____1751
                in
             let body =
               FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty r)
                 (FStar_Extraction_ML_Syntax.MLE_App (e, vs_es))
                in
             FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t)
               (FStar_Extraction_ML_Syntax.MLE_Fun (vs_ts, body)))
  
let maybe_eta_expand :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr
  =
  fun expect  ->
    fun e  ->
      let uu____1787 =
        (FStar_Options.ml_no_eta_expand_coertions ()) ||
          (let uu____1789 = FStar_Options.codegen ()  in
           uu____1789 = (FStar_Pervasives_Native.Some "Kremlin"))
         in
      if uu____1787 then e else eta_expand expect e
  
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
          let uu____1808 =
            type_leq_c g (FStar_Pervasives_Native.Some e) ty1 expect  in
          match uu____1808 with
          | (true ,FStar_Pervasives_Native.Some e') -> e'
          | uu____1818 ->
              (FStar_Extraction_ML_UEnv.debug g
                 (fun uu____1830  ->
                    let uu____1831 =
                      FStar_Extraction_ML_Code.string_of_mlexpr
                        g.FStar_Extraction_ML_UEnv.currentModule e
                       in
                    let uu____1832 =
                      FStar_Extraction_ML_Code.string_of_mlty
                        g.FStar_Extraction_ML_UEnv.currentModule ty1
                       in
                    let uu____1833 =
                      FStar_Extraction_ML_Code.string_of_mlty
                        g.FStar_Extraction_ML_UEnv.currentModule expect
                       in
                    FStar_Util.print3
                      "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n"
                      uu____1831 uu____1832 uu____1833);
               (let uu____1834 =
                  FStar_All.pipe_left
                    (FStar_Extraction_ML_Syntax.with_ty expect)
                    (FStar_Extraction_ML_Syntax.MLE_Coerce (e, ty1, expect))
                   in
                maybe_eta_expand expect uu____1834))
  
let bv_as_mlty :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlty
  =
  fun g  ->
    fun bv  ->
      let uu____1841 = FStar_Extraction_ML_UEnv.lookup_bv g bv  in
      match uu____1841 with
      | FStar_Util.Inl (uu____1842,t) -> t
      | uu____1856 -> FStar_Extraction_ML_Syntax.MLTY_Top
  
let rec term_as_mlty :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlty
  =
  fun g  ->
    fun t0  ->
      let rec is_top_ty t =
        match t with
        | FStar_Extraction_ML_Syntax.MLTY_Top  -> true
        | FStar_Extraction_ML_Syntax.MLTY_Named uu____1899 ->
            let uu____1906 = FStar_Extraction_ML_Util.udelta_unfold g t  in
            (match uu____1906 with
             | FStar_Pervasives_Native.None  -> false
             | FStar_Pervasives_Native.Some t1 -> is_top_ty t1)
        | uu____1910 -> false  in
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
      let uu____1913 = is_top_ty mlt  in
      if uu____1913
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

and term_as_mlty' :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlty
  =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_bvar uu____1919 ->
          let uu____1920 =
            let uu____1921 = FStar_Syntax_Print.term_to_string t1  in
            FStar_Util.format1 "Impossible: Unexpected term %s" uu____1921
             in
          failwith uu____1920
      | FStar_Syntax_Syntax.Tm_delayed uu____1922 ->
          let uu____1947 =
            let uu____1948 = FStar_Syntax_Print.term_to_string t1  in
            FStar_Util.format1 "Impossible: Unexpected term %s" uu____1948
             in
          failwith uu____1947
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____1949 =
            let uu____1950 = FStar_Syntax_Print.term_to_string t1  in
            FStar_Util.format1 "Impossible: Unexpected term %s" uu____1950
             in
          failwith uu____1949
      | FStar_Syntax_Syntax.Tm_constant uu____1951 ->
          FStar_Extraction_ML_UEnv.unknownType
      | FStar_Syntax_Syntax.Tm_uvar uu____1952 ->
          FStar_Extraction_ML_UEnv.unknownType
      | FStar_Syntax_Syntax.Tm_meta (t2,uu____1970) -> term_as_mlty' env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____1975;
             FStar_Syntax_Syntax.index = uu____1976;
             FStar_Syntax_Syntax.sort = t2;_},uu____1978)
          -> term_as_mlty' env t2
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____1986) -> term_as_mlty' env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____1992,uu____1993) ->
          term_as_mlty' env t2
      | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
      | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv []
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____2060 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____2060 with
           | (bs1,c1) ->
               let uu____2067 = binders_as_ml_binders env bs1  in
               (match uu____2067 with
                | (mlbs,env1) ->
                    let t_ret =
                      let eff =
                        FStar_TypeChecker_Env.norm_eff_name
                          env1.FStar_Extraction_ML_UEnv.tcenv
                          (FStar_Syntax_Util.comp_effect_name c1)
                         in
                      let uu____2094 =
                        let uu____2101 =
                          FStar_TypeChecker_Env.effect_decl_opt
                            env1.FStar_Extraction_ML_UEnv.tcenv eff
                           in
                        FStar_Util.must uu____2101  in
                      match uu____2094 with
                      | (ed,qualifiers) ->
                          let uu____2122 =
                            FStar_All.pipe_right qualifiers
                              (FStar_List.contains
                                 FStar_Syntax_Syntax.Reifiable)
                             in
                          if uu____2122
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
                    let uu____2129 =
                      FStar_List.fold_right
                        (fun uu____2148  ->
                           fun uu____2149  ->
                             match (uu____2148, uu____2149) with
                             | ((uu____2170,t2),(tag,t')) ->
                                 (FStar_Extraction_ML_Syntax.E_PURE,
                                   (FStar_Extraction_ML_Syntax.MLTY_Fun
                                      (t2, tag, t')))) mlbs (erase1, t_ret)
                       in
                    (match uu____2129 with | (uu____2182,t2) -> t2)))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let res =
            let uu____2207 =
              let uu____2208 = FStar_Syntax_Util.un_uinst head1  in
              uu____2208.FStar_Syntax_Syntax.n  in
            match uu____2207 with
            | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
            | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv args
            | FStar_Syntax_Syntax.Tm_app (head2,args') ->
                let uu____2235 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app
                       (head2, (FStar_List.append args' args)))
                    FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   in
                term_as_mlty' env uu____2235
            | uu____2252 -> FStar_Extraction_ML_UEnv.unknownType  in
          res
      | FStar_Syntax_Syntax.Tm_abs (bs,ty,uu____2255) ->
          let uu____2276 = FStar_Syntax_Subst.open_term bs ty  in
          (match uu____2276 with
           | (bs1,ty1) ->
               let uu____2283 = binders_as_ml_binders env bs1  in
               (match uu____2283 with | (bts,env1) -> term_as_mlty' env1 ty1))
      | FStar_Syntax_Syntax.Tm_type uu____2308 ->
          FStar_Extraction_ML_UEnv.unknownType
      | FStar_Syntax_Syntax.Tm_let uu____2309 ->
          FStar_Extraction_ML_UEnv.unknownType
      | FStar_Syntax_Syntax.Tm_match uu____2322 ->
          FStar_Extraction_ML_UEnv.unknownType

and arg_as_mlty :
  FStar_Extraction_ML_UEnv.env ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 -> FStar_Extraction_ML_Syntax.mlty
  =
  fun g  ->
    fun uu____2346  ->
      match uu____2346 with
      | (a,uu____2352) ->
          let uu____2353 = is_type g a  in
          if uu____2353
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
        let uu____2358 =
          let uu____2371 =
            FStar_TypeChecker_Env.lookup_lid g.FStar_Extraction_ML_UEnv.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____2371 with
          | ((uu____2392,fvty),uu____2394) ->
              let fvty1 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Normalize.UnfoldUntil
                     FStar_Syntax_Syntax.Delta_constant]
                  g.FStar_Extraction_ML_UEnv.tcenv fvty
                 in
              FStar_Syntax_Util.arrow_formals fvty1
           in
        match uu____2358 with
        | (formals,uu____2401) ->
            let mlargs = FStar_List.map (arg_as_mlty g) args  in
            let mlargs1 =
              let n_args = FStar_List.length args  in
              if (FStar_List.length formals) > n_args
              then
                let uu____2445 = FStar_Util.first_N n_args formals  in
                match uu____2445 with
                | (uu____2472,rest) ->
                    let uu____2498 =
                      FStar_List.map
                        (fun uu____2506  ->
                           FStar_Extraction_ML_UEnv.erasedContent) rest
                       in
                    FStar_List.append mlargs uu____2498
              else mlargs  in
            let nm =
              let uu____2513 =
                FStar_Extraction_ML_UEnv.maybe_mangle_type_projector g fv  in
              match uu____2513 with
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
      let uu____2531 =
        FStar_All.pipe_right bs
          (FStar_List.fold_left
             (fun uu____2574  ->
                fun b  ->
                  match uu____2574 with
                  | (ml_bs,env) ->
                      let uu____2614 = is_type_binder g b  in
                      if uu____2614
                      then
                        let b1 = FStar_Pervasives_Native.fst b  in
                        let env1 =
                          FStar_Extraction_ML_UEnv.extend_ty env b1
                            (FStar_Pervasives_Native.Some
                               FStar_Extraction_ML_Syntax.MLTY_Top)
                           in
                        let ml_b =
                          let uu____2632 =
                            FStar_Extraction_ML_UEnv.bv_as_ml_termvar b1  in
                          (uu____2632, FStar_Extraction_ML_Syntax.ml_unit_ty)
                           in
                        ((ml_b :: ml_bs), env1)
                      else
                        (let b1 = FStar_Pervasives_Native.fst b  in
                         let t = term_as_mlty env b1.FStar_Syntax_Syntax.sort
                            in
                         let uu____2646 =
                           FStar_Extraction_ML_UEnv.extend_bv env b1 
                             ([], t) false false false
                            in
                         match uu____2646 with
                         | (env1,b2) ->
                             let ml_b =
                               let uu____2670 =
                                 FStar_Extraction_ML_UEnv.removeTick b2  in
                               (uu____2670, t)  in
                             ((ml_b :: ml_bs), env1))) ([], g))
         in
      match uu____2531 with | (ml_bs,env) -> ((FStar_List.rev ml_bs), env)

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
      | (FStar_Extraction_ML_Syntax.MLE_Seq es1,uu____2738) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (FStar_List.append es1 [e2])
      | (uu____2741,FStar_Extraction_ML_Syntax.MLE_Seq es2) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (e1 :: es2)
      | uu____2745 -> FStar_Extraction_ML_Syntax.MLE_Seq [e1; e2]
  
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
                    | uu____2774 when
                        (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
                          =
                          FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr
                        -> body.FStar_Extraction_ML_Syntax.expr
                    | uu____2775 ->
                        mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def
                          body)
             | uu____2776 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body))
        | uu____2779 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body)
  
let resugar_pat :
  FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option ->
    FStar_Extraction_ML_Syntax.mlpattern ->
      FStar_Extraction_ML_Syntax.mlpattern
  =
  fun q  ->
    fun p  ->
      match p with
      | FStar_Extraction_ML_Syntax.MLP_CTor (d,pats) ->
          let uu____2796 = FStar_Extraction_ML_Util.is_xtuple d  in
          (match uu____2796 with
           | FStar_Pervasives_Native.Some n1 ->
               FStar_Extraction_ML_Syntax.MLP_Tuple pats
           | uu____2800 ->
               (match q with
                | FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Record_ctor (ty,fns)) ->
                    let path =
                      FStar_List.map FStar_Ident.text_of_id ty.FStar_Ident.ns
                       in
                    let fs = record_fields fns pats  in
                    FStar_Extraction_ML_Syntax.MLP_Record (path, fs)
                | uu____2827 -> p))
      | uu____2830 -> p
  
let rec extract_one_pat :
  Prims.bool ->
    FStar_Extraction_ML_UEnv.env ->
      FStar_Syntax_Syntax.pat ->
        FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option ->
          (FStar_Extraction_ML_UEnv.env ->
             FStar_Syntax_Syntax.term ->
               (FStar_Extraction_ML_Syntax.mlexpr,FStar_Extraction_ML_Syntax.e_tag,
                 FStar_Extraction_ML_Syntax.mlty)
                 FStar_Pervasives_Native.tuple3)
            ->
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
          fun term_as_mlexpr  ->
            let ok t =
              match expected_topt with
              | FStar_Pervasives_Native.None  -> true
              | FStar_Pervasives_Native.Some t' ->
                  let ok = type_leq g t t'  in
                  (if Prims.op_Negation ok
                   then
                     FStar_Extraction_ML_UEnv.debug g
                       (fun uu____2910  ->
                          let uu____2911 =
                            FStar_Extraction_ML_Code.string_of_mlty
                              g.FStar_Extraction_ML_UEnv.currentModule t'
                             in
                          let uu____2912 =
                            FStar_Extraction_ML_Code.string_of_mlty
                              g.FStar_Extraction_ML_UEnv.currentModule t
                             in
                          FStar_Util.print2
                            "Expected pattern type %s; got pattern type %s\n"
                            uu____2911 uu____2912)
                   else ();
                   ok)
               in
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int
                (c,swopt)) when
                let uu____2942 = FStar_Options.codegen ()  in
                uu____2942 <> (FStar_Pervasives_Native.Some "Kremlin") ->
                let uu____2947 =
                  match swopt with
                  | FStar_Pervasives_Native.None  ->
                      let uu____2960 =
                        let uu____2961 =
                          let uu____2962 =
                            FStar_Extraction_ML_Util.mlconst_of_const
                              p.FStar_Syntax_Syntax.p
                              (FStar_Const.Const_int
                                 (c, FStar_Pervasives_Native.None))
                             in
                          FStar_Extraction_ML_Syntax.MLE_Const uu____2962  in
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.ml_int_ty) uu____2961
                         in
                      (uu____2960, FStar_Extraction_ML_Syntax.ml_int_ty)
                  | FStar_Pervasives_Native.Some sw ->
                      let source_term =
                        FStar_ToSyntax_ToSyntax.desugar_machine_integer
                          (g.FStar_Extraction_ML_UEnv.tcenv).FStar_TypeChecker_Env.dsenv
                          c sw FStar_Range.dummyRange
                         in
                      let uu____2983 = term_as_mlexpr g source_term  in
                      (match uu____2983 with
                       | (mlterm,uu____2995,mlty) -> (mlterm, mlty))
                   in
                (match uu____2947 with
                 | (mlc,ml_ty) ->
                     let x = FStar_Extraction_ML_Syntax.gensym ()  in
                     let when_clause =
                       let uu____3015 =
                         let uu____3016 =
                           let uu____3023 =
                             let uu____3026 =
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty ml_ty)
                                 (FStar_Extraction_ML_Syntax.MLE_Var x)
                                in
                             [uu____3026; mlc]  in
                           (FStar_Extraction_ML_Util.prims_op_equality,
                             uu____3023)
                            in
                         FStar_Extraction_ML_Syntax.MLE_App uu____3016  in
                       FStar_All.pipe_left
                         (FStar_Extraction_ML_Syntax.with_ty
                            FStar_Extraction_ML_Syntax.ml_bool_ty) uu____3015
                        in
                     let uu____3029 = ok ml_ty  in
                     (g,
                       (FStar_Pervasives_Native.Some
                          ((FStar_Extraction_ML_Syntax.MLP_Var x),
                            [when_clause])), uu____3029))
            | FStar_Syntax_Syntax.Pat_constant s ->
                let t =
                  FStar_TypeChecker_TcTerm.tc_constant
                    g.FStar_Extraction_ML_UEnv.tcenv FStar_Range.dummyRange s
                   in
                let mlty = term_as_mlty g t  in
                let uu____3049 =
                  let uu____3058 =
                    let uu____3065 =
                      let uu____3066 =
                        FStar_Extraction_ML_Util.mlconst_of_const
                          p.FStar_Syntax_Syntax.p s
                         in
                      FStar_Extraction_ML_Syntax.MLP_Const uu____3066  in
                    (uu____3065, [])  in
                  FStar_Pervasives_Native.Some uu____3058  in
                let uu____3075 = ok mlty  in (g, uu____3049, uu____3075)
            | FStar_Syntax_Syntax.Pat_var x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort  in
                let uu____3086 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp
                   in
                (match uu____3086 with
                 | (g1,x1) ->
                     let uu____3109 = ok mlty  in
                     (g1,
                       (if imp
                        then FStar_Pervasives_Native.None
                        else
                          FStar_Pervasives_Native.Some
                            ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                       uu____3109))
            | FStar_Syntax_Syntax.Pat_wild x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort  in
                let uu____3143 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp
                   in
                (match uu____3143 with
                 | (g1,x1) ->
                     let uu____3166 = ok mlty  in
                     (g1,
                       (if imp
                        then FStar_Pervasives_Native.None
                        else
                          FStar_Pervasives_Native.Some
                            ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                       uu____3166))
            | FStar_Syntax_Syntax.Pat_dot_term uu____3198 ->
                (g, FStar_Pervasives_Native.None, true)
            | FStar_Syntax_Syntax.Pat_cons (f,pats) ->
                let uu____3237 =
                  let uu____3242 = FStar_Extraction_ML_UEnv.lookup_fv g f  in
                  match uu____3242 with
                  | FStar_Util.Inr
                      (uu____3247,{
                                    FStar_Extraction_ML_Syntax.expr =
                                      FStar_Extraction_ML_Syntax.MLE_Name n1;
                                    FStar_Extraction_ML_Syntax.mlty =
                                      uu____3249;
                                    FStar_Extraction_ML_Syntax.loc =
                                      uu____3250;_},ttys,uu____3252)
                      -> (n1, ttys)
                  | uu____3265 -> failwith "Expected a constructor"  in
                (match uu____3237 with
                 | (d,tys) ->
                     let nTyVars =
                       FStar_List.length (FStar_Pervasives_Native.fst tys)
                        in
                     let uu____3287 = FStar_Util.first_N nTyVars pats  in
                     (match uu____3287 with
                      | (tysVarPats,restPats) ->
                          let f_ty_opt =
                            try
                              let mlty_args =
                                FStar_All.pipe_right tysVarPats
                                  (FStar_List.map
                                     (fun uu____3420  ->
                                        match uu____3420 with
                                        | (p1,uu____3428) ->
                                            (match p1.FStar_Syntax_Syntax.v
                                             with
                                             | FStar_Syntax_Syntax.Pat_dot_term
                                                 (uu____3433,t) ->
                                                 term_as_mlty g t
                                             | uu____3439 ->
                                                 (FStar_Extraction_ML_UEnv.debug
                                                    g
                                                    (fun uu____3443  ->
                                                       let uu____3444 =
                                                         FStar_Syntax_Print.pat_to_string
                                                           p1
                                                          in
                                                       FStar_Util.print1
                                                         "Pattern %s is not extractable"
                                                         uu____3444);
                                                  FStar_Exn.raise
                                                    Un_extractable))))
                                 in
                              let f_ty =
                                FStar_Extraction_ML_Util.subst tys mlty_args
                                 in
                              let uu____3446 =
                                FStar_Extraction_ML_Util.uncurry_mlty_fun
                                  f_ty
                                 in
                              FStar_Pervasives_Native.Some uu____3446
                            with
                            | Un_extractable  -> FStar_Pervasives_Native.None
                             in
                          let uu____3475 =
                            FStar_Util.fold_map
                              (fun g1  ->
                                 fun uu____3511  ->
                                   match uu____3511 with
                                   | (p1,imp1) ->
                                       let uu____3530 =
                                         extract_one_pat true g1 p1
                                           FStar_Pervasives_Native.None
                                           term_as_mlexpr
                                          in
                                       (match uu____3530 with
                                        | (g2,p2,uu____3559) -> (g2, p2))) g
                              tysVarPats
                             in
                          (match uu____3475 with
                           | (g1,tyMLPats) ->
                               let uu____3620 =
                                 FStar_Util.fold_map
                                   (fun uu____3684  ->
                                      fun uu____3685  ->
                                        match (uu____3684, uu____3685) with
                                        | ((g2,f_ty_opt1),(p1,imp1)) ->
                                            let uu____3778 =
                                              match f_ty_opt1 with
                                              | FStar_Pervasives_Native.Some
                                                  (hd1::rest,res) ->
                                                  ((FStar_Pervasives_Native.Some
                                                      (rest, res)),
                                                    (FStar_Pervasives_Native.Some
                                                       hd1))
                                              | uu____3838 ->
                                                  (FStar_Pervasives_Native.None,
                                                    FStar_Pervasives_Native.None)
                                               in
                                            (match uu____3778 with
                                             | (f_ty_opt2,expected_ty) ->
                                                 let uu____3909 =
                                                   extract_one_pat false g2
                                                     p1 expected_ty
                                                     term_as_mlexpr
                                                    in
                                                 (match uu____3909 with
                                                  | (g3,p2,uu____3950) ->
                                                      ((g3, f_ty_opt2), p2))))
                                   (g1, f_ty_opt) restPats
                                  in
                               (match uu____3620 with
                                | ((g2,f_ty_opt1),restMLPats) ->
                                    let uu____4068 =
                                      let uu____4079 =
                                        FStar_All.pipe_right
                                          (FStar_List.append tyMLPats
                                             restMLPats)
                                          (FStar_List.collect
                                             (fun uu___291_4130  ->
                                                match uu___291_4130 with
                                                | FStar_Pervasives_Native.Some
                                                    x -> [x]
                                                | uu____4172 -> []))
                                         in
                                      FStar_All.pipe_right uu____4079
                                        FStar_List.split
                                       in
                                    (match uu____4068 with
                                     | (mlPats,when_clauses) ->
                                         let pat_ty_compat =
                                           match f_ty_opt1 with
                                           | FStar_Pervasives_Native.Some
                                               ([],t) -> ok t
                                           | uu____4245 -> false  in
                                         let uu____4254 =
                                           let uu____4263 =
                                             let uu____4270 =
                                               resugar_pat
                                                 f.FStar_Syntax_Syntax.fv_qual
                                                 (FStar_Extraction_ML_Syntax.MLP_CTor
                                                    (d, mlPats))
                                                in
                                             let uu____4273 =
                                               FStar_All.pipe_right
                                                 when_clauses
                                                 FStar_List.flatten
                                                in
                                             (uu____4270, uu____4273)  in
                                           FStar_Pervasives_Native.Some
                                             uu____4263
                                            in
                                         (g2, uu____4254, pat_ty_compat))))))
  
let extract_pat :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.pat ->
      FStar_Extraction_ML_Syntax.mlty ->
        (FStar_Extraction_ML_UEnv.env ->
           FStar_Syntax_Syntax.term ->
             (FStar_Extraction_ML_Syntax.mlexpr,FStar_Extraction_ML_Syntax.e_tag,
               FStar_Extraction_ML_Syntax.mlty)
               FStar_Pervasives_Native.tuple3)
          ->
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
        fun term_as_mlexpr  ->
          let extract_one_pat1 g1 p1 expected_t1 =
            let uu____4386 =
              extract_one_pat false g1 p1 expected_t1 term_as_mlexpr  in
            match uu____4386 with
            | (g2,FStar_Pervasives_Native.Some (x,v1),b) -> (g2, (x, v1), b)
            | uu____4443 ->
                failwith "Impossible: Unable to translate pattern"
             in
          let mk_when_clause whens =
            match whens with
            | [] -> FStar_Pervasives_Native.None
            | hd1::tl1 ->
                let uu____4486 =
                  FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd1
                    tl1
                   in
                FStar_Pervasives_Native.Some uu____4486
             in
          let uu____4487 =
            extract_one_pat1 g p (FStar_Pervasives_Native.Some expected_t)
             in
          match uu____4487 with
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
            | FStar_Extraction_ML_Syntax.MLTY_Fun (t0,uu____4625,t1) ->
                let x = FStar_Extraction_ML_Syntax.gensym ()  in
                let uu____4628 =
                  let uu____4639 =
                    let uu____4648 =
                      FStar_All.pipe_left
                        (FStar_Extraction_ML_Syntax.with_ty t0)
                        (FStar_Extraction_ML_Syntax.MLE_Var x)
                       in
                    ((x, t0), uu____4648)  in
                  uu____4639 :: more_args  in
                eta_args uu____4628 t1
            | FStar_Extraction_ML_Syntax.MLTY_Named (uu____4661,uu____4662)
                -> ((FStar_List.rev more_args), t)
            | uu____4685 -> failwith "Impossible: Head type is not an arrow"
             in
          let as_record qual1 e =
            match ((e.FStar_Extraction_ML_Syntax.expr), qual1) with
            | (FStar_Extraction_ML_Syntax.MLE_CTor
               (uu____4713,args),FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Record_ctor (tyname,fields))) ->
                let path =
                  FStar_List.map FStar_Ident.text_of_id tyname.FStar_Ident.ns
                   in
                let fields1 = record_fields fields args  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     e.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_Record (path, fields1))
            | uu____4745 -> e  in
          let resugar_and_maybe_eta qual1 e =
            let uu____4763 = eta_args [] residualType  in
            match uu____4763 with
            | (eargs,tres) ->
                (match eargs with
                 | [] ->
                     let uu____4816 = as_record qual1 e  in
                     FStar_Extraction_ML_Util.resugar_exp uu____4816
                 | uu____4817 ->
                     let uu____4828 = FStar_List.unzip eargs  in
                     (match uu____4828 with
                      | (binders,eargs1) ->
                          (match e.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_CTor (head1,args)
                               ->
                               let body =
                                 let uu____4870 =
                                   let uu____4871 =
                                     FStar_All.pipe_left
                                       (FStar_Extraction_ML_Syntax.with_ty
                                          tres)
                                       (FStar_Extraction_ML_Syntax.MLE_CTor
                                          (head1,
                                            (FStar_List.append args eargs1)))
                                      in
                                   FStar_All.pipe_left (as_record qual1)
                                     uu____4871
                                    in
                                 FStar_All.pipe_left
                                   FStar_Extraction_ML_Util.resugar_exp
                                   uu____4870
                                  in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    e.FStar_Extraction_ML_Syntax.mlty)
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    (binders, body))
                           | uu____4880 ->
                               failwith "Impossible: Not a constructor")))
             in
          match ((mlAppExpr.FStar_Extraction_ML_Syntax.expr), qual) with
          | (uu____4883,FStar_Pervasives_Native.None ) -> mlAppExpr
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____4887;
                FStar_Extraction_ML_Syntax.loc = uu____4888;_},mle::args),FStar_Pervasives_Native.Some
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
                | uu____4915 ->
                    let uu____4918 =
                      let uu____4925 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj
                         in
                      (uu____4925, args)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____4918
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
                     FStar_Extraction_ML_Syntax.mlty = uu____4929;
                     FStar_Extraction_ML_Syntax.loc = uu____4930;_},uu____4931);
                FStar_Extraction_ML_Syntax.mlty = uu____4932;
                FStar_Extraction_ML_Syntax.loc = uu____4933;_},mle::args),FStar_Pervasives_Native.Some
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
                | uu____4964 ->
                    let uu____4967 =
                      let uu____4974 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj
                         in
                      (uu____4974, args)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____4967
                 in
              FStar_Extraction_ML_Syntax.with_ty
                mlAppExpr.FStar_Extraction_ML_Syntax.mlty e
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____4978;
                FStar_Extraction_ML_Syntax.loc = uu____4979;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____4987 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____4987
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____4991;
                FStar_Extraction_ML_Syntax.loc = uu____4992;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____4994)) ->
              let uu____5007 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5007
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____5011;
                     FStar_Extraction_ML_Syntax.loc = uu____5012;_},uu____5013);
                FStar_Extraction_ML_Syntax.mlty = uu____5014;
                FStar_Extraction_ML_Syntax.loc = uu____5015;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____5027 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5027
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____5031;
                     FStar_Extraction_ML_Syntax.loc = uu____5032;_},uu____5033);
                FStar_Extraction_ML_Syntax.mlty = uu____5034;
                FStar_Extraction_ML_Syntax.loc = uu____5035;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____5037)) ->
              let uu____5054 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5054
          | (FStar_Extraction_ML_Syntax.MLE_Name
             mlp,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor
             )) ->
              let uu____5060 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5060
          | (FStar_Extraction_ML_Syntax.MLE_Name
             mlp,FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____5064)) ->
              let uu____5073 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5073
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____5077;
                FStar_Extraction_ML_Syntax.loc = uu____5078;_},uu____5079),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____5086 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5086
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____5090;
                FStar_Extraction_ML_Syntax.loc = uu____5091;_},uu____5092),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____5093)) ->
              let uu____5106 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5106
          | uu____5109 -> mlAppExpr
  
let maybe_downgrade_eff :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.e_tag ->
      FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.e_tag
  =
  fun g  ->
    fun f  ->
      fun t  ->
        let uu____5125 =
          (f = FStar_Extraction_ML_Syntax.E_GHOST) &&
            (type_leq g t FStar_Extraction_ML_Syntax.ml_unit_ty)
           in
        if uu____5125 then FStar_Extraction_ML_Syntax.E_PURE else f
  
let rec term_as_mlexpr :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Extraction_ML_Syntax.mlexpr,FStar_Extraction_ML_Syntax.e_tag,
        FStar_Extraction_ML_Syntax.mlty) FStar_Pervasives_Native.tuple3
  =
  fun g  ->
    fun t  ->
      let uu____5179 = term_as_mlexpr' g t  in
      match uu____5179 with
      | (e,tag,ty) ->
          let tag1 = maybe_downgrade_eff g tag ty  in
          (FStar_Extraction_ML_UEnv.debug g
             (fun u  ->
                let uu____5200 =
                  let uu____5201 = FStar_Syntax_Print.tag_of_term t  in
                  let uu____5202 = FStar_Syntax_Print.term_to_string t  in
                  let uu____5203 =
                    FStar_Extraction_ML_Code.string_of_mlty
                      g.FStar_Extraction_ML_UEnv.currentModule ty
                     in
                  FStar_Util.format4
                    "term_as_mlexpr (%s) :  %s has ML type %s and effect %s\n"
                    uu____5201 uu____5202 uu____5203
                    (FStar_Extraction_ML_Util.eff_to_string tag1)
                   in
                FStar_Util.print_string uu____5200);
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
          let uu____5212 = check_term_as_mlexpr' g t f ty  in
          match uu____5212 with
          | (e,t1) ->
              let uu____5223 = erase g e t1 f  in
              (match uu____5223 with | (r,uu____5235,t2) -> (r, t2))

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
          let uu____5245 = term_as_mlexpr g e0  in
          match uu____5245 with
          | (e,tag,t) ->
              let tag1 = maybe_downgrade_eff g tag t  in
              if FStar_Extraction_ML_Util.eff_leq tag1 f
              then
                let uu____5264 = maybe_coerce g e t ty  in (uu____5264, ty)
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
           let uu____5282 =
             let uu____5283 =
               FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos  in
             let uu____5284 = FStar_Syntax_Print.tag_of_term top  in
             let uu____5285 = FStar_Syntax_Print.term_to_string top  in
             FStar_Util.format3 "%s: term_as_mlexpr' (%s) :  %s \n"
               uu____5283 uu____5284 uu____5285
              in
           FStar_Util.print_string uu____5282);
      (let t = FStar_Syntax_Subst.compress top  in
       match t.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____5293 =
             let uu____5294 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5294
              in
           failwith uu____5293
       | FStar_Syntax_Syntax.Tm_delayed uu____5301 ->
           let uu____5326 =
             let uu____5327 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5327
              in
           failwith uu____5326
       | FStar_Syntax_Syntax.Tm_uvar uu____5334 ->
           let uu____5351 =
             let uu____5352 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5352
              in
           failwith uu____5351
       | FStar_Syntax_Syntax.Tm_bvar uu____5359 ->
           let uu____5360 =
             let uu____5361 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5361
              in
           failwith uu____5360
       | FStar_Syntax_Syntax.Tm_type uu____5368 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_refine uu____5369 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_arrow uu____5376 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Mutable_alloc ))
           ->
           let uu____5394 = term_as_mlexpr' g t1  in
           (match uu____5394 with
            | ({
                 FStar_Extraction_ML_Syntax.expr =
                   FStar_Extraction_ML_Syntax.MLE_Let
                   ((FStar_Extraction_ML_Syntax.NonRec ,flags1,bodies),continuation);
                 FStar_Extraction_ML_Syntax.mlty = mlty;
                 FStar_Extraction_ML_Syntax.loc = loc;_},tag,typ)
                ->
                ({
                   FStar_Extraction_ML_Syntax.expr =
                     (FStar_Extraction_ML_Syntax.MLE_Let
                        ((FStar_Extraction_ML_Syntax.NonRec,
                           (FStar_Extraction_ML_Syntax.Mutable :: flags1),
                           bodies), continuation));
                   FStar_Extraction_ML_Syntax.mlty = mlty;
                   FStar_Extraction_ML_Syntax.loc = loc
                 }, tag, typ)
            | uu____5440 -> failwith "impossible")
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_monadic (m,uu____5455)) ->
           let t2 = FStar_Syntax_Subst.compress t1  in
           (match t2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) when
                FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname ->
                let uu____5485 =
                  let uu____5492 =
                    FStar_TypeChecker_Env.effect_decl_opt
                      g.FStar_Extraction_ML_UEnv.tcenv m
                     in
                  FStar_Util.must uu____5492  in
                (match uu____5485 with
                 | (ed,qualifiers) ->
                     let uu____5519 =
                       let uu____5520 =
                         FStar_All.pipe_right qualifiers
                           (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                          in
                       FStar_All.pipe_right uu____5520 Prims.op_Negation  in
                     if uu____5519
                     then term_as_mlexpr' g t2
                     else
                       failwith
                         "This should not happen (should have been handled at Tm_abs level)")
            | uu____5536 -> term_as_mlexpr' g t2)
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____5538) -> term_as_mlexpr' g t1
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____5544) -> term_as_mlexpr' g t1
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____5550 =
             FStar_TypeChecker_TcTerm.type_of_tot_term
               g.FStar_Extraction_ML_UEnv.tcenv t
              in
           (match uu____5550 with
            | (uu____5563,ty,uu____5565) ->
                let ml_ty = term_as_mlty g ty  in
                let uu____5567 =
                  let uu____5568 =
                    FStar_Extraction_ML_Util.mlexpr_of_const
                      t.FStar_Syntax_Syntax.pos c
                     in
                  FStar_Extraction_ML_Syntax.with_ty ml_ty uu____5568  in
                (uu____5567, FStar_Extraction_ML_Syntax.E_PURE, ml_ty))
       | FStar_Syntax_Syntax.Tm_name uu____5569 ->
           let uu____5570 = is_type g t  in
           if uu____5570
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____5578 = FStar_Extraction_ML_UEnv.lookup_term g t  in
              match uu____5578 with
              | (FStar_Util.Inl uu____5591,uu____5592) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | (FStar_Util.Inr (uu____5629,x,mltys,uu____5632),qual) ->
                  (match mltys with
                   | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                       ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | ([],t1) ->
                       let uu____5678 =
                         maybe_eta_data_and_project_record g qual t1 x  in
                       (uu____5678, FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | uu____5679 -> err_uninst g t mltys t))
       | FStar_Syntax_Syntax.Tm_fvar uu____5686 ->
           let uu____5687 = is_type g t  in
           if uu____5687
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____5695 = FStar_Extraction_ML_UEnv.lookup_term g t  in
              match uu____5695 with
              | (FStar_Util.Inl uu____5708,uu____5709) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | (FStar_Util.Inr (uu____5746,x,mltys,uu____5749),qual) ->
                  (match mltys with
                   | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                       ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | ([],t1) ->
                       let uu____5795 =
                         maybe_eta_data_and_project_record g qual t1 x  in
                       (uu____5795, FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | uu____5796 -> err_uninst g t mltys t))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,copt) ->
           let uu____5826 = FStar_Syntax_Subst.open_term bs body  in
           (match uu____5826 with
            | (bs1,body1) ->
                let uu____5839 = binders_as_ml_binders g bs1  in
                (match uu____5839 with
                 | (ml_bs,env) ->
                     let body2 =
                       match copt with
                       | FStar_Pervasives_Native.Some c ->
                           let uu____5872 =
                             FStar_TypeChecker_Env.is_reifiable
                               env.FStar_Extraction_ML_UEnv.tcenv c
                              in
                           if uu____5872
                           then
                             FStar_TypeChecker_Util.reify_body
                               env.FStar_Extraction_ML_UEnv.tcenv body1
                           else body1
                       | FStar_Pervasives_Native.None  ->
                           (FStar_Extraction_ML_UEnv.debug g
                              (fun uu____5877  ->
                                 let uu____5878 =
                                   FStar_Syntax_Print.term_to_string body1
                                    in
                                 FStar_Util.print1
                                   "No computation type for: %s\n" uu____5878);
                            body1)
                        in
                     let uu____5879 = term_as_mlexpr env body2  in
                     (match uu____5879 with
                      | (ml_body,f,t1) ->
                          let uu____5895 =
                            FStar_List.fold_right
                              (fun uu____5914  ->
                                 fun uu____5915  ->
                                   match (uu____5914, uu____5915) with
                                   | ((uu____5936,targ),(f1,t2)) ->
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         (FStar_Extraction_ML_Syntax.MLTY_Fun
                                            (targ, f1, t2)))) ml_bs (f, t1)
                             in
                          (match uu____5895 with
                           | (f1,tfun) ->
                               let uu____5956 =
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty tfun)
                                   (FStar_Extraction_ML_Syntax.MLE_Fun
                                      (ml_bs, ml_body))
                                  in
                               (uu____5956, f1, tfun)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____5963;
              FStar_Syntax_Syntax.vars = uu____5964;_},(a1,uu____5966)::[])
           ->
           let ty =
             let uu____5996 =
               FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid  in
             term_as_mlty g uu____5996  in
           let uu____5997 =
             let uu____5998 =
               FStar_Extraction_ML_Util.mlexpr_of_range
                 a1.FStar_Syntax_Syntax.pos
                in
             FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty)
               uu____5998
              in
           (uu____5997, FStar_Extraction_ML_Syntax.E_PURE, ty)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____5999;
              FStar_Syntax_Syntax.vars = uu____6000;_},(a1,uu____6002)::
            (a2,uu____6004)::[])
           -> term_as_mlexpr' g a1
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____6043);
              FStar_Syntax_Syntax.pos = uu____6044;
              FStar_Syntax_Syntax.vars = uu____6045;_},uu____6046)
           -> failwith "Unreachable? Tm_app Const_reflect"
       | FStar_Syntax_Syntax.Tm_app (head1,uu____6074::(v1,uu____6076)::[])
           when (FStar_Syntax_Util.is_fstar_tactics_embed head1) && false ->
           let uu____6117 =
             let uu____6120 = FStar_Syntax_Print.term_to_string v1  in
             FStar_Util.format2 "Trying to extract a quotation of %s"
               uu____6120
              in
           let s =
             let uu____6122 =
               let uu____6123 =
                 let uu____6124 =
                   let uu____6127 = FStar_Util.marshal v1  in
                   FStar_Util.bytes_of_string uu____6127  in
                 FStar_Extraction_ML_Syntax.MLC_Bytes uu____6124  in
               FStar_Extraction_ML_Syntax.MLE_Const uu____6123  in
             FStar_Extraction_ML_Syntax.with_ty
               FStar_Extraction_ML_Syntax.ml_string_ty uu____6122
              in
           let zero1 =
             FStar_Extraction_ML_Syntax.with_ty
               FStar_Extraction_ML_Syntax.ml_int_ty
               (FStar_Extraction_ML_Syntax.MLE_Const
                  (FStar_Extraction_ML_Syntax.MLC_Int
                     ("0", FStar_Pervasives_Native.None)))
              in
           let term_ty =
             let uu____6142 =
               FStar_Syntax_Syntax.fvar
                 FStar_Parser_Const.fstar_syntax_syntax_term
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None
                in
             term_as_mlty g uu____6142  in
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
           let uu____6147 =
             FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty term_ty)
               (FStar_Extraction_ML_Syntax.MLE_App
                  (marshal_from_string, [s; zero1]))
              in
           (uu____6147, FStar_Extraction_ML_Syntax.E_PURE, term_ty)
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let is_total rc =
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_Tot_lid)
               ||
               (FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
                  (FStar_List.existsb
                     (fun uu___292_6179  ->
                        match uu___292_6179 with
                        | FStar_Syntax_Syntax.TOTAL  -> true
                        | uu____6180 -> false)))
              in
           let uu____6181 =
             let uu____6186 =
               let uu____6187 = FStar_Syntax_Subst.compress head1  in
               uu____6187.FStar_Syntax_Syntax.n  in
             ((head1.FStar_Syntax_Syntax.n), uu____6186)  in
           (match uu____6181 with
            | (FStar_Syntax_Syntax.Tm_uvar uu____6196,uu____6197) ->
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
            | (uu____6215,FStar_Syntax_Syntax.Tm_abs
               (bs,uu____6217,FStar_Pervasives_Native.Some rc)) when
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
            | (uu____6238,FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_reify )) ->
                let e =
                  let uu____6240 = FStar_List.hd args  in
                  FStar_TypeChecker_Util.reify_body_with_arg
                    g.FStar_Extraction_ML_UEnv.tcenv head1 uu____6240
                   in
                let tm =
                  let uu____6250 =
                    let uu____6251 = FStar_TypeChecker_Util.remove_reify e
                       in
                    let uu____6252 = FStar_List.tl args  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____6251 uu____6252  in
                  uu____6250 FStar_Pervasives_Native.None
                    t.FStar_Syntax_Syntax.pos
                   in
                term_as_mlexpr' g tm
            | uu____6261 ->
                let rec extract_app is_data uu____6306 uu____6307 restArgs =
                  match (uu____6306, uu____6307) with
                  | ((mlhead,mlargs_f),(f,t1)) ->
                      (match (restArgs, t1) with
                       | ([],uu____6397) ->
                           let evaluation_order_guaranteed =
                             (((FStar_List.length mlargs_f) =
                                 (Prims.parse_int "1"))
                                || (FStar_Options.codegen_fsharp ()))
                               ||
                               (match head1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_fvar fv ->
                                    (FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.op_And)
                                      ||
                                      (FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.op_Or)
                                | uu____6419 -> false)
                              in
                           let uu____6420 =
                             if evaluation_order_guaranteed
                             then
                               let uu____6445 =
                                 FStar_All.pipe_right
                                   (FStar_List.rev mlargs_f)
                                   (FStar_List.map
                                      FStar_Pervasives_Native.fst)
                                  in
                               ([], uu____6445)
                             else
                               FStar_List.fold_left
                                 (fun uu____6499  ->
                                    fun uu____6500  ->
                                      match (uu____6499, uu____6500) with
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
                                             let uu____6603 =
                                               let uu____6606 =
                                                 FStar_All.pipe_left
                                                   (FStar_Extraction_ML_Syntax.with_ty
                                                      arg.FStar_Extraction_ML_Syntax.mlty)
                                                   (FStar_Extraction_ML_Syntax.MLE_Var
                                                      x)
                                                  in
                                               uu____6606 :: out_args  in
                                             (((x, arg) :: lbs), uu____6603)))
                                 ([], []) mlargs_f
                              in
                           (match uu____6420 with
                            | (lbs,mlargs) ->
                                let app =
                                  let uu____6656 =
                                    FStar_All.pipe_left
                                      (FStar_Extraction_ML_Syntax.with_ty t1)
                                      (FStar_Extraction_ML_Syntax.MLE_App
                                         (mlhead, mlargs))
                                     in
                                  FStar_All.pipe_left
                                    (maybe_eta_data_and_project_record g
                                       is_data t1) uu____6656
                                   in
                                let l_app =
                                  FStar_List.fold_right
                                    (fun uu____6668  ->
                                       fun out  ->
                                         match uu____6668 with
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
                       | ((arg,uu____6689)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                          (formal_t,f',t2)) when
                           (is_type g arg) &&
                             (type_leq g formal_t
                                FStar_Extraction_ML_Syntax.ml_unit_ty)
                           ->
                           let uu____6720 =
                             let uu____6725 =
                               FStar_Extraction_ML_Util.join
                                 arg.FStar_Syntax_Syntax.pos f f'
                                in
                             (uu____6725, t2)  in
                           extract_app is_data
                             (mlhead,
                               ((FStar_Extraction_ML_Syntax.ml_unit,
                                  FStar_Extraction_ML_Syntax.E_PURE) ::
                               mlargs_f)) uu____6720 rest
                       | ((e0,uu____6737)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                          (tExpected,f',t2)) ->
                           let r = e0.FStar_Syntax_Syntax.pos  in
                           let uu____6769 = term_as_mlexpr g e0  in
                           (match uu____6769 with
                            | (e01,f0,tInferred) ->
                                let e02 =
                                  maybe_coerce g e01 tInferred tExpected  in
                                let uu____6786 =
                                  let uu____6791 =
                                    FStar_Extraction_ML_Util.join_l r
                                      [f; f'; f0]
                                     in
                                  (uu____6791, t2)  in
                                extract_app is_data
                                  (mlhead, ((e02, f0) :: mlargs_f))
                                  uu____6786 rest)
                       | uu____6802 ->
                           let uu____6815 =
                             FStar_Extraction_ML_Util.udelta_unfold g t1  in
                           (match uu____6815 with
                            | FStar_Pervasives_Native.Some t2 ->
                                extract_app is_data (mlhead, mlargs_f)
                                  (f, t2) restArgs
                            | FStar_Pervasives_Native.None  ->
                                err_ill_typed_application g top restArgs t1))
                   in
                let extract_app_maybe_projector is_data mlhead uu____6872
                  args1 =
                  match uu____6872 with
                  | (f,t1) ->
                      (match is_data with
                       | FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_projector uu____6904)
                           ->
                           let rec remove_implicits args2 f1 t2 =
                             match (args2, t2) with
                             | ((a0,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____6982))::args3,FStar_Extraction_ML_Syntax.MLTY_Fun
                                (uu____6984,f',t3)) ->
                                 let uu____7021 =
                                   FStar_Extraction_ML_Util.join
                                     a0.FStar_Syntax_Syntax.pos f1 f'
                                    in
                                 remove_implicits args3 uu____7021 t3
                             | uu____7022 -> (args2, f1, t2)  in
                           let uu____7047 = remove_implicits args1 f t1  in
                           (match uu____7047 with
                            | (args2,f1,t2) ->
                                extract_app is_data (mlhead, []) (f1, t2)
                                  args2)
                       | uu____7103 ->
                           extract_app is_data (mlhead, []) (f, t1) args1)
                   in
                let uu____7116 = is_type g t  in
                if uu____7116
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
                         (let uu____7133 =
                            let uu____7134 =
                              FStar_Extraction_ML_Syntax.string_of_mlpath
                                g.FStar_Extraction_ML_UEnv.currentModule
                               in
                            uu____7134 = "FStar.Tactics.Builtins"  in
                          Prims.op_Negation uu____7133)
                       ->
                       (match args with
                        | a::b::[] ->
                            term_as_mlexpr g (FStar_Pervasives_Native.fst a)
                        | uu____7175 ->
                            let uu____7184 =
                              FStar_Syntax_Print.args_to_string args  in
                            failwith uu____7184)
                   | FStar_Syntax_Syntax.Tm_name uu____7191 ->
                       let uu____7192 =
                         let uu____7205 =
                           FStar_Extraction_ML_UEnv.lookup_term g head2  in
                         match uu____7205 with
                         | (FStar_Util.Inr (uu____7224,x1,x2,x3),q) ->
                             ((x1, x2, x3), q)
                         | uu____7269 -> failwith "FIXME Ty"  in
                       (match uu____7192 with
                        | ((head_ml,(vars,t1),inst_ok),qual) ->
                            let has_typ_apps =
                              match args with
                              | (a,uu____7319)::uu____7320 -> is_type g a
                              | uu____7339 -> false  in
                            let uu____7348 =
                              match vars with
                              | uu____7377::uu____7378 when
                                  (Prims.op_Negation has_typ_apps) && inst_ok
                                  -> (head_ml, t1, args)
                              | uu____7389 ->
                                  let n1 = FStar_List.length vars  in
                                  if n1 <= (FStar_List.length args)
                                  then
                                    let uu____7417 =
                                      FStar_Util.first_N n1 args  in
                                    (match uu____7417 with
                                     | (prefix1,rest) ->
                                         let prefixAsMLTypes =
                                           FStar_List.map
                                             (fun uu____7506  ->
                                                match uu____7506 with
                                                | (x,uu____7512) ->
                                                    term_as_mlty g x) prefix1
                                            in
                                         let t2 =
                                           instantiate (vars, t1)
                                             prefixAsMLTypes
                                            in
                                         let mk_tapp e ty_args =
                                           match ty_args with
                                           | [] -> e
                                           | uu____7525 ->
                                               let uu___296_7528 = e  in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (FStar_Extraction_ML_Syntax.MLE_TApp
                                                      (e, ty_args));
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   =
                                                   (uu___296_7528.FStar_Extraction_ML_Syntax.mlty);
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___296_7528.FStar_Extraction_ML_Syntax.loc)
                                               }
                                            in
                                         let head3 =
                                           match head_ml.FStar_Extraction_ML_Syntax.expr
                                           with
                                           | FStar_Extraction_ML_Syntax.MLE_Name
                                               uu____7532 ->
                                               let uu___297_7533 =
                                                 mk_tapp head_ml
                                                   prefixAsMLTypes
                                                  in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (uu___297_7533.FStar_Extraction_ML_Syntax.expr);
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   = t2;
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___297_7533.FStar_Extraction_ML_Syntax.loc)
                                               }
                                           | FStar_Extraction_ML_Syntax.MLE_Var
                                               uu____7534 ->
                                               let uu___297_7535 =
                                                 mk_tapp head_ml
                                                   prefixAsMLTypes
                                                  in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (uu___297_7535.FStar_Extraction_ML_Syntax.expr);
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   = t2;
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___297_7535.FStar_Extraction_ML_Syntax.loc)
                                               }
                                           | FStar_Extraction_ML_Syntax.MLE_App
                                               (head3,{
                                                        FStar_Extraction_ML_Syntax.expr
                                                          =
                                                          FStar_Extraction_ML_Syntax.MLE_Const
                                                          (FStar_Extraction_ML_Syntax.MLC_Unit
                                                          );
                                                        FStar_Extraction_ML_Syntax.mlty
                                                          = uu____7537;
                                                        FStar_Extraction_ML_Syntax.loc
                                                          = uu____7538;_}::[])
                                               ->
                                               FStar_All.pipe_right
                                                 (FStar_Extraction_ML_Syntax.MLE_App
                                                    ((let uu___298_7544 =
                                                        mk_tapp head3
                                                          prefixAsMLTypes
                                                         in
                                                      {
                                                        FStar_Extraction_ML_Syntax.expr
                                                          =
                                                          (uu___298_7544.FStar_Extraction_ML_Syntax.expr);
                                                        FStar_Extraction_ML_Syntax.mlty
                                                          =
                                                          (FStar_Extraction_ML_Syntax.MLTY_Fun
                                                             (FStar_Extraction_ML_Syntax.ml_unit_ty,
                                                               FStar_Extraction_ML_Syntax.E_PURE,
                                                               t2));
                                                        FStar_Extraction_ML_Syntax.loc
                                                          =
                                                          (uu___298_7544.FStar_Extraction_ML_Syntax.loc)
                                                      }),
                                                      [FStar_Extraction_ML_Syntax.ml_unit]))
                                                 (FStar_Extraction_ML_Syntax.with_ty
                                                    t2)
                                           | uu____7545 ->
                                               failwith
                                                 "Impossible: Unexpected head term"
                                            in
                                         (head3, t2, rest))
                                  else err_uninst g head2 (vars, t1) top
                               in
                            (match uu____7348 with
                             | (head_ml1,head_t,args1) ->
                                 (match args1 with
                                  | [] ->
                                      let uu____7606 =
                                        maybe_eta_data_and_project_record g
                                          qual head_t head_ml1
                                         in
                                      (uu____7606,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        head_t)
                                  | uu____7607 ->
                                      extract_app_maybe_projector qual
                                        head_ml1
                                        (FStar_Extraction_ML_Syntax.E_PURE,
                                          head_t) args1)))
                   | FStar_Syntax_Syntax.Tm_fvar uu____7616 ->
                       let uu____7617 =
                         let uu____7630 =
                           FStar_Extraction_ML_UEnv.lookup_term g head2  in
                         match uu____7630 with
                         | (FStar_Util.Inr (uu____7649,x1,x2,x3),q) ->
                             ((x1, x2, x3), q)
                         | uu____7694 -> failwith "FIXME Ty"  in
                       (match uu____7617 with
                        | ((head_ml,(vars,t1),inst_ok),qual) ->
                            let has_typ_apps =
                              match args with
                              | (a,uu____7744)::uu____7745 -> is_type g a
                              | uu____7764 -> false  in
                            let uu____7773 =
                              match vars with
                              | uu____7802::uu____7803 when
                                  (Prims.op_Negation has_typ_apps) && inst_ok
                                  -> (head_ml, t1, args)
                              | uu____7814 ->
                                  let n1 = FStar_List.length vars  in
                                  if n1 <= (FStar_List.length args)
                                  then
                                    let uu____7842 =
                                      FStar_Util.first_N n1 args  in
                                    (match uu____7842 with
                                     | (prefix1,rest) ->
                                         let prefixAsMLTypes =
                                           FStar_List.map
                                             (fun uu____7931  ->
                                                match uu____7931 with
                                                | (x,uu____7937) ->
                                                    term_as_mlty g x) prefix1
                                            in
                                         let t2 =
                                           instantiate (vars, t1)
                                             prefixAsMLTypes
                                            in
                                         let mk_tapp e ty_args =
                                           match ty_args with
                                           | [] -> e
                                           | uu____7950 ->
                                               let uu___296_7953 = e  in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (FStar_Extraction_ML_Syntax.MLE_TApp
                                                      (e, ty_args));
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   =
                                                   (uu___296_7953.FStar_Extraction_ML_Syntax.mlty);
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___296_7953.FStar_Extraction_ML_Syntax.loc)
                                               }
                                            in
                                         let head3 =
                                           match head_ml.FStar_Extraction_ML_Syntax.expr
                                           with
                                           | FStar_Extraction_ML_Syntax.MLE_Name
                                               uu____7957 ->
                                               let uu___297_7958 =
                                                 mk_tapp head_ml
                                                   prefixAsMLTypes
                                                  in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (uu___297_7958.FStar_Extraction_ML_Syntax.expr);
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   = t2;
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___297_7958.FStar_Extraction_ML_Syntax.loc)
                                               }
                                           | FStar_Extraction_ML_Syntax.MLE_Var
                                               uu____7959 ->
                                               let uu___297_7960 =
                                                 mk_tapp head_ml
                                                   prefixAsMLTypes
                                                  in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (uu___297_7960.FStar_Extraction_ML_Syntax.expr);
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   = t2;
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___297_7960.FStar_Extraction_ML_Syntax.loc)
                                               }
                                           | FStar_Extraction_ML_Syntax.MLE_App
                                               (head3,{
                                                        FStar_Extraction_ML_Syntax.expr
                                                          =
                                                          FStar_Extraction_ML_Syntax.MLE_Const
                                                          (FStar_Extraction_ML_Syntax.MLC_Unit
                                                          );
                                                        FStar_Extraction_ML_Syntax.mlty
                                                          = uu____7962;
                                                        FStar_Extraction_ML_Syntax.loc
                                                          = uu____7963;_}::[])
                                               ->
                                               FStar_All.pipe_right
                                                 (FStar_Extraction_ML_Syntax.MLE_App
                                                    ((let uu___298_7969 =
                                                        mk_tapp head3
                                                          prefixAsMLTypes
                                                         in
                                                      {
                                                        FStar_Extraction_ML_Syntax.expr
                                                          =
                                                          (uu___298_7969.FStar_Extraction_ML_Syntax.expr);
                                                        FStar_Extraction_ML_Syntax.mlty
                                                          =
                                                          (FStar_Extraction_ML_Syntax.MLTY_Fun
                                                             (FStar_Extraction_ML_Syntax.ml_unit_ty,
                                                               FStar_Extraction_ML_Syntax.E_PURE,
                                                               t2));
                                                        FStar_Extraction_ML_Syntax.loc
                                                          =
                                                          (uu___298_7969.FStar_Extraction_ML_Syntax.loc)
                                                      }),
                                                      [FStar_Extraction_ML_Syntax.ml_unit]))
                                                 (FStar_Extraction_ML_Syntax.with_ty
                                                    t2)
                                           | uu____7970 ->
                                               failwith
                                                 "Impossible: Unexpected head term"
                                            in
                                         (head3, t2, rest))
                                  else err_uninst g head2 (vars, t1) top
                               in
                            (match uu____7773 with
                             | (head_ml1,head_t,args1) ->
                                 (match args1 with
                                  | [] ->
                                      let uu____8031 =
                                        maybe_eta_data_and_project_record g
                                          qual head_t head_ml1
                                         in
                                      (uu____8031,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        head_t)
                                  | uu____8032 ->
                                      extract_app_maybe_projector qual
                                        head_ml1
                                        (FStar_Extraction_ML_Syntax.E_PURE,
                                          head_t) args1)))
                   | uu____8041 ->
                       let uu____8042 = term_as_mlexpr g head2  in
                       (match uu____8042 with
                        | (head3,f,t1) ->
                            extract_app_maybe_projector
                              FStar_Pervasives_Native.None head3 (f, t1) args)))
       | FStar_Syntax_Syntax.Tm_ascribed (e0,(tc,uu____8060),f) ->
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
           let uu____8127 = check_term_as_mlexpr g e0 f1 t1  in
           (match uu____8127 with | (e,t2) -> (e, f1, t2))
       | FStar_Syntax_Syntax.Tm_let ((is_rec,lbs),e') ->
           let top_level = FStar_Syntax_Syntax.is_top_level lbs  in
           let uu____8158 =
             if is_rec
             then FStar_Syntax_Subst.open_let_rec lbs e'
             else
               (let uu____8172 = FStar_Syntax_Syntax.is_top_level lbs  in
                if uu____8172
                then (lbs, e')
                else
                  (let lb = FStar_List.hd lbs  in
                   let x =
                     let uu____8186 =
                       FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                     FStar_Syntax_Syntax.freshen_bv uu____8186  in
                   let lb1 =
                     let uu___299_8188 = lb  in
                     {
                       FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                       FStar_Syntax_Syntax.lbunivs =
                         (uu___299_8188.FStar_Syntax_Syntax.lbunivs);
                       FStar_Syntax_Syntax.lbtyp =
                         (uu___299_8188.FStar_Syntax_Syntax.lbtyp);
                       FStar_Syntax_Syntax.lbeff =
                         (uu___299_8188.FStar_Syntax_Syntax.lbeff);
                       FStar_Syntax_Syntax.lbdef =
                         (uu___299_8188.FStar_Syntax_Syntax.lbdef)
                     }  in
                   let e'1 =
                     FStar_Syntax_Subst.subst
                       [FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x)] e'
                      in
                   ([lb1], e'1)))
              in
           (match uu____8158 with
            | (lbs1,e'1) ->
                let lbs2 =
                  if top_level
                  then
                    FStar_All.pipe_right lbs1
                      (FStar_List.map
                         (fun lb  ->
                            let tcenv =
                              let uu____8220 =
                                FStar_Ident.lid_of_path
                                  (FStar_List.append
                                     (FStar_Pervasives_Native.fst
                                        g.FStar_Extraction_ML_UEnv.currentModule)
                                     [FStar_Pervasives_Native.snd
                                        g.FStar_Extraction_ML_UEnv.currentModule])
                                  FStar_Range.dummyRange
                                 in
                              FStar_TypeChecker_Env.set_current_module
                                g.FStar_Extraction_ML_UEnv.tcenv uu____8220
                               in
                            FStar_Extraction_ML_UEnv.debug g
                              (fun uu____8227  ->
                                 FStar_Options.set_option "debug_level"
                                   (FStar_Options.List
                                      [FStar_Options.String "Norm";
                                      FStar_Options.String "Extraction"]));
                            (let lbdef =
                               let uu____8231 = FStar_Options.ml_ish ()  in
                               if uu____8231
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
                             let uu___300_8235 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___300_8235.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___300_8235.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___300_8235.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___300_8235.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef
                             })))
                  else lbs1  in
                let maybe_generalize uu____8258 =
                  match uu____8258 with
                  | { FStar_Syntax_Syntax.lbname = lbname_;
                      FStar_Syntax_Syntax.lbunivs = uu____8278;
                      FStar_Syntax_Syntax.lbtyp = t1;
                      FStar_Syntax_Syntax.lbeff = lbeff;
                      FStar_Syntax_Syntax.lbdef = e;_} ->
                      let f_e = effect_as_etag g lbeff  in
                      let t2 = FStar_Syntax_Subst.compress t1  in
                      (match t2.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                           let uu____8348 = FStar_List.hd bs  in
                           FStar_All.pipe_right uu____8348 (is_type_binder g)
                           ->
                           let uu____8361 = FStar_Syntax_Subst.open_comp bs c
                              in
                           (match uu____8361 with
                            | (bs1,c1) ->
                                let uu____8386 =
                                  let uu____8393 =
                                    FStar_Util.prefix_until
                                      (fun x  ->
                                         let uu____8429 = is_type_binder g x
                                            in
                                         Prims.op_Negation uu____8429) bs1
                                     in
                                  match uu____8393 with
                                  | FStar_Pervasives_Native.None  ->
                                      (bs1,
                                        (FStar_Syntax_Util.comp_result c1))
                                  | FStar_Pervasives_Native.Some (bs2,b,rest)
                                      ->
                                      let uu____8517 =
                                        FStar_Syntax_Util.arrow (b :: rest)
                                          c1
                                         in
                                      (bs2, uu____8517)
                                   in
                                (match uu____8386 with
                                 | (tbinders,tbody) ->
                                     let n_tbinders =
                                       FStar_List.length tbinders  in
                                     let e1 =
                                       let uu____8562 = normalize_abs e  in
                                       FStar_All.pipe_right uu____8562
                                         FStar_Syntax_Util.unmeta
                                        in
                                     (match e1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Tm_abs
                                          (bs2,body,copt) ->
                                          let uu____8604 =
                                            FStar_Syntax_Subst.open_term bs2
                                              body
                                             in
                                          (match uu____8604 with
                                           | (bs3,body1) ->
                                               if
                                                 n_tbinders <=
                                                   (FStar_List.length bs3)
                                               then
                                                 let uu____8657 =
                                                   FStar_Util.first_N
                                                     n_tbinders bs3
                                                    in
                                                 (match uu____8657 with
                                                  | (targs,rest_args) ->
                                                      let expected_source_ty
                                                        =
                                                        let s =
                                                          FStar_List.map2
                                                            (fun uu____8745 
                                                               ->
                                                               fun uu____8746
                                                                  ->
                                                                 match 
                                                                   (uu____8745,
                                                                    uu____8746)
                                                                 with
                                                                 | ((x,uu____8764),
                                                                    (y,uu____8766))
                                                                    ->
                                                                    let uu____8775
                                                                    =
                                                                    let uu____8782
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    y  in
                                                                    (x,
                                                                    uu____8782)
                                                                     in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____8775)
                                                            tbinders targs
                                                           in
                                                        FStar_Syntax_Subst.subst
                                                          s tbody
                                                         in
                                                      let env =
                                                        FStar_List.fold_left
                                                          (fun env  ->
                                                             fun uu____8793 
                                                               ->
                                                               match uu____8793
                                                               with
                                                               | (a,uu____8799)
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
                                                        let uu____8808 =
                                                          FStar_All.pipe_right
                                                            targs
                                                            (FStar_List.map
                                                               (fun
                                                                  uu____8826 
                                                                  ->
                                                                  match uu____8826
                                                                  with
                                                                  | (x,uu____8832)
                                                                    ->
                                                                    FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                                    x))
                                                           in
                                                        (uu____8808,
                                                          expected_t)
                                                         in
                                                      let add_unit =
                                                        match rest_args with
                                                        | [] ->
                                                            let uu____8840 =
                                                              is_fstar_value
                                                                body1
                                                               in
                                                            Prims.op_Negation
                                                              uu____8840
                                                        | uu____8841 -> false
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
                                          uu____8910 ->
                                          let env =
                                            FStar_List.fold_left
                                              (fun env  ->
                                                 fun uu____8927  ->
                                                   match uu____8927 with
                                                   | (a,uu____8933) ->
                                                       FStar_Extraction_ML_UEnv.extend_ty
                                                         env a
                                                         FStar_Pervasives_Native.None)
                                              g tbinders
                                             in
                                          let expected_t =
                                            term_as_mlty env tbody  in
                                          let polytype =
                                            let uu____8942 =
                                              FStar_All.pipe_right tbinders
                                                (FStar_List.map
                                                   (fun uu____8954  ->
                                                      match uu____8954 with
                                                      | (x,uu____8960) ->
                                                          FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                            x))
                                               in
                                            (uu____8942, expected_t)  in
                                          let args =
                                            FStar_All.pipe_right tbinders
                                              (FStar_List.map
                                                 (fun uu____8976  ->
                                                    match uu____8976 with
                                                    | (bv,uu____8982) ->
                                                        let uu____8983 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            bv
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____8983
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
                                          uu____9025 ->
                                          let env =
                                            FStar_List.fold_left
                                              (fun env  ->
                                                 fun uu____9036  ->
                                                   match uu____9036 with
                                                   | (a,uu____9042) ->
                                                       FStar_Extraction_ML_UEnv.extend_ty
                                                         env a
                                                         FStar_Pervasives_Native.None)
                                              g tbinders
                                             in
                                          let expected_t =
                                            term_as_mlty env tbody  in
                                          let polytype =
                                            let uu____9051 =
                                              FStar_All.pipe_right tbinders
                                                (FStar_List.map
                                                   (fun uu____9063  ->
                                                      match uu____9063 with
                                                      | (x,uu____9069) ->
                                                          FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                            x))
                                               in
                                            (uu____9051, expected_t)  in
                                          let args =
                                            FStar_All.pipe_right tbinders
                                              (FStar_List.map
                                                 (fun uu____9085  ->
                                                    match uu____9085 with
                                                    | (bv,uu____9091) ->
                                                        let uu____9092 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            bv
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____9092
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
                                          uu____9134 ->
                                          let env =
                                            FStar_List.fold_left
                                              (fun env  ->
                                                 fun uu____9145  ->
                                                   match uu____9145 with
                                                   | (a,uu____9151) ->
                                                       FStar_Extraction_ML_UEnv.extend_ty
                                                         env a
                                                         FStar_Pervasives_Native.None)
                                              g tbinders
                                             in
                                          let expected_t =
                                            term_as_mlty env tbody  in
                                          let polytype =
                                            let uu____9160 =
                                              FStar_All.pipe_right tbinders
                                                (FStar_List.map
                                                   (fun uu____9172  ->
                                                      match uu____9172 with
                                                      | (x,uu____9178) ->
                                                          FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                            x))
                                               in
                                            (uu____9160, expected_t)  in
                                          let args =
                                            FStar_All.pipe_right tbinders
                                              (FStar_List.map
                                                 (fun uu____9194  ->
                                                    match uu____9194 with
                                                    | (bv,uu____9200) ->
                                                        let uu____9201 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            bv
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____9201
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
                                      | uu____9243 ->
                                          err_value_restriction e1)))
                       | uu____9262 ->
                           let expected_t = term_as_mlty g t2  in
                           (lbname_, f_e, (t2, ([], ([], expected_t))),
                             false, e))
                   in
                let check_lb env uu____9366 =
                  match uu____9366 with
                  | (nm,(lbname,f,(t1,(targs,polytype)),add_unit,e)) ->
                      let env1 =
                        FStar_List.fold_left
                          (fun env1  ->
                             fun uu____9501  ->
                               match uu____9501 with
                               | (a,uu____9507) ->
                                   FStar_Extraction_ML_UEnv.extend_ty env1 a
                                     FStar_Pervasives_Native.None) env targs
                         in
                      let expected_t = FStar_Pervasives_Native.snd polytype
                         in
                      let uu____9509 =
                        check_term_as_mlexpr env1 e f expected_t  in
                      (match uu____9509 with
                       | (e1,uu____9519) ->
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
                let uu____9586 =
                  FStar_List.fold_right
                    (fun lb  ->
                       fun uu____9677  ->
                         match uu____9677 with
                         | (env,lbs4) ->
                             let uu____9802 = lb  in
                             (match uu____9802 with
                              | (lbname,uu____9850,(t1,(uu____9852,polytype)),add_unit,uu____9855)
                                  ->
                                  let uu____9868 =
                                    FStar_Extraction_ML_UEnv.extend_lb env
                                      lbname t1 polytype add_unit true
                                     in
                                  (match uu____9868 with
                                   | (env1,nm) -> (env1, ((nm, lb) :: lbs4)))))
                    lbs3 (g, [])
                   in
                (match uu____9586 with
                 | (env_body,lbs4) ->
                     let env_def = if is_rec then env_body else g  in
                     let lbs5 =
                       FStar_All.pipe_right lbs4
                         (FStar_List.map (check_lb env_def))
                        in
                     let e'_rng = e'1.FStar_Syntax_Syntax.pos  in
                     let uu____10145 = term_as_mlexpr env_body e'1  in
                     (match uu____10145 with
                      | (e'2,f',t') ->
                          let f =
                            let uu____10162 =
                              let uu____10165 =
                                FStar_List.map FStar_Pervasives_Native.fst
                                  lbs5
                                 in
                              f' :: uu____10165  in
                            FStar_Extraction_ML_Util.join_l e'_rng
                              uu____10162
                             in
                          let is_rec1 =
                            if is_rec = true
                            then FStar_Extraction_ML_Syntax.Rec
                            else FStar_Extraction_ML_Syntax.NonRec  in
                          let uu____10174 =
                            let uu____10175 =
                              let uu____10176 =
                                let uu____10177 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    lbs5
                                   in
                                (is_rec1, [], uu____10177)  in
                              mk_MLE_Let top_level uu____10176 e'2  in
                            let uu____10188 =
                              FStar_Extraction_ML_Util.mlloc_of_range
                                t.FStar_Syntax_Syntax.pos
                               in
                            FStar_Extraction_ML_Syntax.with_ty_loc t'
                              uu____10175 uu____10188
                             in
                          (uu____10174, f, t'))))
       | FStar_Syntax_Syntax.Tm_match (scrutinee,pats) ->
           let uu____10227 = term_as_mlexpr g scrutinee  in
           (match uu____10227 with
            | (e,f_e,t_e) ->
                let uu____10243 = check_pats_for_ite pats  in
                (match uu____10243 with
                 | (b,then_e,else_e) ->
                     let no_lift x t1 = x  in
                     if b
                     then
                       (match (then_e, else_e) with
                        | (FStar_Pervasives_Native.Some
                           then_e1,FStar_Pervasives_Native.Some else_e1) ->
                            let uu____10300 = term_as_mlexpr g then_e1  in
                            (match uu____10300 with
                             | (then_mle,f_then,t_then) ->
                                 let uu____10316 = term_as_mlexpr g else_e1
                                    in
                                 (match uu____10316 with
                                  | (else_mle,f_else,t_else) ->
                                      let uu____10332 =
                                        let uu____10341 =
                                          type_leq g t_then t_else  in
                                        if uu____10341
                                        then (t_else, no_lift)
                                        else
                                          (let uu____10355 =
                                             type_leq g t_else t_then  in
                                           if uu____10355
                                           then (t_then, no_lift)
                                           else
                                             (FStar_Extraction_ML_Syntax.MLTY_Top,
                                               FStar_Extraction_ML_Syntax.apply_obj_repr))
                                         in
                                      (match uu____10332 with
                                       | (t_branch,maybe_lift1) ->
                                           let uu____10389 =
                                             let uu____10390 =
                                               let uu____10391 =
                                                 let uu____10400 =
                                                   maybe_lift1 then_mle
                                                     t_then
                                                    in
                                                 let uu____10401 =
                                                   let uu____10404 =
                                                     maybe_lift1 else_mle
                                                       t_else
                                                      in
                                                   FStar_Pervasives_Native.Some
                                                     uu____10404
                                                    in
                                                 (e, uu____10400,
                                                   uu____10401)
                                                  in
                                               FStar_Extraction_ML_Syntax.MLE_If
                                                 uu____10391
                                                in
                                             FStar_All.pipe_left
                                               (FStar_Extraction_ML_Syntax.with_ty
                                                  t_branch) uu____10390
                                              in
                                           let uu____10407 =
                                             FStar_Extraction_ML_Util.join
                                               then_e1.FStar_Syntax_Syntax.pos
                                               f_then f_else
                                              in
                                           (uu____10389, uu____10407,
                                             t_branch))))
                        | uu____10408 ->
                            failwith
                              "ITE pats matched but then and else expressions not found?")
                     else
                       (let uu____10424 =
                          FStar_All.pipe_right pats
                            (FStar_Util.fold_map
                               (fun compat  ->
                                  fun br  ->
                                    let uu____10533 =
                                      FStar_Syntax_Subst.open_branch br  in
                                    match uu____10533 with
                                    | (pat,when_opt,branch1) ->
                                        let uu____10577 =
                                          extract_pat g pat t_e
                                            term_as_mlexpr
                                           in
                                        (match uu____10577 with
                                         | (env,p,pat_t_compat) ->
                                             let uu____10635 =
                                               match when_opt with
                                               | FStar_Pervasives_Native.None
                                                    ->
                                                   (FStar_Pervasives_Native.None,
                                                     FStar_Extraction_ML_Syntax.E_PURE)
                                               | FStar_Pervasives_Native.Some
                                                   w ->
                                                   let uu____10657 =
                                                     term_as_mlexpr env w  in
                                                   (match uu____10657 with
                                                    | (w1,f_w,t_w) ->
                                                        let w2 =
                                                          maybe_coerce env w1
                                                            t_w
                                                            FStar_Extraction_ML_Syntax.ml_bool_ty
                                                           in
                                                        ((FStar_Pervasives_Native.Some
                                                            w2), f_w))
                                                in
                                             (match uu____10635 with
                                              | (when_opt1,f_when) ->
                                                  let uu____10706 =
                                                    term_as_mlexpr env
                                                      branch1
                                                     in
                                                  (match uu____10706 with
                                                   | (mlbranch,f_branch,t_branch)
                                                       ->
                                                       let uu____10740 =
                                                         FStar_All.pipe_right
                                                           p
                                                           (FStar_List.map
                                                              (fun
                                                                 uu____10817 
                                                                 ->
                                                                 match uu____10817
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
                                                         uu____10740)))))
                               true)
                           in
                        match uu____10424 with
                        | (pat_t_compat,mlbranches) ->
                            let mlbranches1 = FStar_List.flatten mlbranches
                               in
                            let e1 =
                              if pat_t_compat
                              then e
                              else
                                (FStar_Extraction_ML_UEnv.debug g
                                   (fun uu____10982  ->
                                      let uu____10983 =
                                        FStar_Extraction_ML_Code.string_of_mlexpr
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          e
                                         in
                                      let uu____10984 =
                                        FStar_Extraction_ML_Code.string_of_mlty
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          t_e
                                         in
                                      FStar_Util.print2
                                        "Coercing scrutinee %s from type %s because pattern type is incompatible\n"
                                        uu____10983 uu____10984);
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty t_e)
                                   (FStar_Extraction_ML_Syntax.MLE_Coerce
                                      (e, t_e,
                                        FStar_Extraction_ML_Syntax.MLTY_Top)))
                               in
                            (match mlbranches1 with
                             | [] ->
                                 let uu____11009 =
                                   let uu____11018 =
                                     let uu____11035 =
                                       FStar_Syntax_Syntax.lid_as_fv
                                         FStar_Parser_Const.failwith_lid
                                         FStar_Syntax_Syntax.Delta_constant
                                         FStar_Pervasives_Native.None
                                        in
                                     FStar_Extraction_ML_UEnv.lookup_fv g
                                       uu____11035
                                      in
                                   FStar_All.pipe_left FStar_Util.right
                                     uu____11018
                                    in
                                 (match uu____11009 with
                                  | (uu____11078,fw,uu____11080,uu____11081)
                                      ->
                                      let uu____11082 =
                                        let uu____11083 =
                                          let uu____11084 =
                                            let uu____11091 =
                                              let uu____11094 =
                                                FStar_All.pipe_left
                                                  (FStar_Extraction_ML_Syntax.with_ty
                                                     FStar_Extraction_ML_Syntax.ml_string_ty)
                                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                                     (FStar_Extraction_ML_Syntax.MLC_String
                                                        "unreachable"))
                                                 in
                                              [uu____11094]  in
                                            (fw, uu____11091)  in
                                          FStar_Extraction_ML_Syntax.MLE_App
                                            uu____11084
                                           in
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             FStar_Extraction_ML_Syntax.ml_unit_ty)
                                          uu____11083
                                         in
                                      (uu____11082,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        FStar_Extraction_ML_Syntax.ml_unit_ty))
                             | (uu____11097,uu____11098,(uu____11099,f_first,t_first))::rest
                                 ->
                                 let uu____11159 =
                                   FStar_List.fold_left
                                     (fun uu____11201  ->
                                        fun uu____11202  ->
                                          match (uu____11201, uu____11202)
                                          with
                                          | ((topt,f),(uu____11259,uu____11260,
                                                       (uu____11261,f_branch,t_branch)))
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
                                                    let uu____11317 =
                                                      type_leq g t1 t_branch
                                                       in
                                                    if uu____11317
                                                    then
                                                      FStar_Pervasives_Native.Some
                                                        t_branch
                                                    else
                                                      (let uu____11321 =
                                                         type_leq g t_branch
                                                           t1
                                                          in
                                                       if uu____11321
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
                                 (match uu____11159 with
                                  | (topt,f_match) ->
                                      let mlbranches2 =
                                        FStar_All.pipe_right mlbranches1
                                          (FStar_List.map
                                             (fun uu____11416  ->
                                                match uu____11416 with
                                                | (p,(wopt,uu____11445),
                                                   (b1,uu____11447,t1)) ->
                                                    let b2 =
                                                      match topt with
                                                      | FStar_Pervasives_Native.None
                                                           ->
                                                          FStar_Extraction_ML_Syntax.apply_obj_repr
                                                            b1 t1
                                                      | FStar_Pervasives_Native.Some
                                                          uu____11466 -> b1
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
                                      let uu____11471 =
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             t_match)
                                          (FStar_Extraction_ML_Syntax.MLE_Match
                                             (e1, mlbranches2))
                                         in
                                      (uu____11471, f_match, t_match)))))))

let ind_discriminator_body :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlmodule1
  =
  fun env  ->
    fun discName  ->
      fun constrName  ->
        let uu____11491 =
          let uu____11496 =
            FStar_TypeChecker_Env.lookup_lid
              env.FStar_Extraction_ML_UEnv.tcenv discName
             in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____11496  in
        match uu____11491 with
        | (uu____11521,fstar_disc_type) ->
            let wildcards =
              let uu____11530 =
                let uu____11531 = FStar_Syntax_Subst.compress fstar_disc_type
                   in
                uu____11531.FStar_Syntax_Syntax.n  in
              match uu____11530 with
              | FStar_Syntax_Syntax.Tm_arrow (binders,uu____11541) ->
                  let uu____11558 =
                    FStar_All.pipe_right binders
                      (FStar_List.filter
                         (fun uu___293_11590  ->
                            match uu___293_11590 with
                            | (uu____11597,FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____11598)) ->
                                true
                            | uu____11601 -> false))
                     in
                  FStar_All.pipe_right uu____11558
                    (FStar_List.map
                       (fun uu____11634  ->
                          let uu____11641 = fresh "_"  in
                          (uu____11641, FStar_Extraction_ML_Syntax.MLTY_Top)))
              | uu____11642 -> failwith "Discriminator must be a function"
               in
            let mlid = fresh "_discr_"  in
            let targ = FStar_Extraction_ML_Syntax.MLTY_Top  in
            let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top  in
            let discrBody =
              let uu____11653 =
                let uu____11654 =
                  let uu____11665 =
                    let uu____11666 =
                      let uu____11667 =
                        let uu____11682 =
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty targ)
                            (FStar_Extraction_ML_Syntax.MLE_Name ([], mlid))
                           in
                        let uu____11685 =
                          let uu____11696 =
                            let uu____11705 =
                              let uu____11706 =
                                let uu____11713 =
                                  FStar_Extraction_ML_Syntax.mlpath_of_lident
                                    constrName
                                   in
                                (uu____11713,
                                  [FStar_Extraction_ML_Syntax.MLP_Wild])
                                 in
                              FStar_Extraction_ML_Syntax.MLP_CTor uu____11706
                               in
                            let uu____11716 =
                              FStar_All.pipe_left
                                (FStar_Extraction_ML_Syntax.with_ty
                                   FStar_Extraction_ML_Syntax.ml_bool_ty)
                                (FStar_Extraction_ML_Syntax.MLE_Const
                                   (FStar_Extraction_ML_Syntax.MLC_Bool true))
                               in
                            (uu____11705, FStar_Pervasives_Native.None,
                              uu____11716)
                             in
                          let uu____11719 =
                            let uu____11730 =
                              let uu____11739 =
                                FStar_All.pipe_left
                                  (FStar_Extraction_ML_Syntax.with_ty
                                     FStar_Extraction_ML_Syntax.ml_bool_ty)
                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                     (FStar_Extraction_ML_Syntax.MLC_Bool
                                        false))
                                 in
                              (FStar_Extraction_ML_Syntax.MLP_Wild,
                                FStar_Pervasives_Native.None, uu____11739)
                               in
                            [uu____11730]  in
                          uu____11696 :: uu____11719  in
                        (uu____11682, uu____11685)  in
                      FStar_Extraction_ML_Syntax.MLE_Match uu____11667  in
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.ml_bool_ty) uu____11666
                     in
                  ((FStar_List.append wildcards [(mlid, targ)]), uu____11665)
                   in
                FStar_Extraction_ML_Syntax.MLE_Fun uu____11654  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty disc_ty) uu____11653
               in
            let uu____11794 =
              let uu____11795 =
                let uu____11798 =
                  let uu____11799 =
                    FStar_Extraction_ML_UEnv.convIdent
                      discName.FStar_Ident.ident
                     in
                  {
                    FStar_Extraction_ML_Syntax.mllb_name = uu____11799;
                    FStar_Extraction_ML_Syntax.mllb_tysc =
                      FStar_Pervasives_Native.None;
                    FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                    FStar_Extraction_ML_Syntax.mllb_def = discrBody;
                    FStar_Extraction_ML_Syntax.print_typ = false
                  }  in
                [uu____11798]  in
              (FStar_Extraction_ML_Syntax.NonRec, [], uu____11795)  in
            FStar_Extraction_ML_Syntax.MLM_Let uu____11794
  