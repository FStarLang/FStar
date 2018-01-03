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
    (let uu____1341 =
       let uu____1342 = FStar_ST.op_Bang c  in
       FStar_Util.string_of_int uu____1342  in
     Prims.strcat x uu____1341)
  
let normalize_abs : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t0  ->
    let rec aux bs t copt =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_abs (bs',body,copt1) ->
          aux (FStar_List.append bs bs') body copt1
      | uu____1470 ->
          let e' = FStar_Syntax_Util.unascribe t1  in
          let uu____1472 = FStar_Syntax_Util.is_fun e'  in
          if uu____1472
          then aux bs e' copt
          else FStar_Syntax_Util.abs bs e' copt
       in
    aux [] t0 FStar_Pervasives_Native.None
  
let unit_binder : FStar_Syntax_Syntax.binder =
  let uu____1478 =
    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
      FStar_Syntax_Syntax.t_unit
     in
  FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____1478 
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
      (let uu____1556 = FStar_List.hd l  in
       match uu____1556 with
       | (p1,w1,e1) ->
           let uu____1590 =
             let uu____1599 = FStar_List.tl l  in FStar_List.hd uu____1599
              in
           (match uu____1590 with
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
                 | uu____1673 -> def)))
  
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
            let uu____1730 = erasable g f ty  in
            if uu____1730
            then
              let uu____1731 =
                type_leq g ty FStar_Extraction_ML_Syntax.ml_unit_ty  in
              (if uu____1731
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
      let uu____1740 = FStar_Extraction_ML_Util.doms_and_cod t  in
      match uu____1740 with
      | (ts,r) ->
          if ts = []
          then e
          else
            (let vs = FStar_List.map (fun uu____1760  -> fresh "a") ts  in
             let vs_ts = FStar_List.zip vs ts  in
             let vs_es =
               let uu____1771 = FStar_List.zip vs ts  in
               FStar_List.map
                 (fun uu____1785  ->
                    match uu____1785 with
                    | (v1,t1) ->
                        FStar_Extraction_ML_Syntax.with_ty t1
                          (FStar_Extraction_ML_Syntax.MLE_Var v1)) uu____1771
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
      let uu____1807 =
        (FStar_Options.ml_no_eta_expand_coertions ()) ||
          (let uu____1809 = FStar_Options.codegen ()  in
           uu____1809 = (FStar_Pervasives_Native.Some "Kremlin"))
         in
      if uu____1807 then e else eta_expand expect e
  
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
          let uu____1828 =
            type_leq_c g (FStar_Pervasives_Native.Some e) ty1 expect  in
          match uu____1828 with
          | (true ,FStar_Pervasives_Native.Some e') -> e'
          | uu____1838 ->
              (FStar_Extraction_ML_UEnv.debug g
                 (fun uu____1850  ->
                    let uu____1851 =
                      FStar_Extraction_ML_Code.string_of_mlexpr
                        g.FStar_Extraction_ML_UEnv.currentModule e
                       in
                    let uu____1852 =
                      FStar_Extraction_ML_Code.string_of_mlty
                        g.FStar_Extraction_ML_UEnv.currentModule ty1
                       in
                    let uu____1853 =
                      FStar_Extraction_ML_Code.string_of_mlty
                        g.FStar_Extraction_ML_UEnv.currentModule expect
                       in
                    FStar_Util.print3
                      "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n"
                      uu____1851 uu____1852 uu____1853);
               (let uu____1854 =
                  FStar_All.pipe_left
                    (FStar_Extraction_ML_Syntax.with_ty expect)
                    (FStar_Extraction_ML_Syntax.MLE_Coerce (e, ty1, expect))
                   in
                maybe_eta_expand expect uu____1854))
  
let bv_as_mlty :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlty
  =
  fun g  ->
    fun bv  ->
      let uu____1861 = FStar_Extraction_ML_UEnv.lookup_bv g bv  in
      match uu____1861 with
      | FStar_Util.Inl (uu____1862,t) -> t
      | uu____1876 -> FStar_Extraction_ML_Syntax.MLTY_Top
  
let rec term_as_mlty :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlty
  =
  fun g  ->
    fun t0  ->
      let rec is_top_ty t =
        match t with
        | FStar_Extraction_ML_Syntax.MLTY_Top  -> true
        | FStar_Extraction_ML_Syntax.MLTY_Named uu____1919 ->
            let uu____1926 = FStar_Extraction_ML_Util.udelta_unfold g t  in
            (match uu____1926 with
             | FStar_Pervasives_Native.None  -> false
             | FStar_Pervasives_Native.Some t1 -> is_top_ty t1)
        | uu____1930 -> false  in
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
      let uu____1933 = is_top_ty mlt  in
      if uu____1933
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
      | FStar_Syntax_Syntax.Tm_bvar uu____1939 ->
          let uu____1940 =
            let uu____1941 = FStar_Syntax_Print.term_to_string t1  in
            FStar_Util.format1 "Impossible: Unexpected term %s" uu____1941
             in
          failwith uu____1940
      | FStar_Syntax_Syntax.Tm_delayed uu____1942 ->
          let uu____1967 =
            let uu____1968 = FStar_Syntax_Print.term_to_string t1  in
            FStar_Util.format1 "Impossible: Unexpected term %s" uu____1968
             in
          failwith uu____1967
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____1969 =
            let uu____1970 = FStar_Syntax_Print.term_to_string t1  in
            FStar_Util.format1 "Impossible: Unexpected term %s" uu____1970
             in
          failwith uu____1969
      | FStar_Syntax_Syntax.Tm_constant uu____1971 ->
          FStar_Extraction_ML_UEnv.unknownType
      | FStar_Syntax_Syntax.Tm_uvar uu____1972 ->
          FStar_Extraction_ML_UEnv.unknownType
      | FStar_Syntax_Syntax.Tm_meta (t2,uu____1990) -> term_as_mlty' env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____1995;
             FStar_Syntax_Syntax.index = uu____1996;
             FStar_Syntax_Syntax.sort = t2;_},uu____1998)
          -> term_as_mlty' env t2
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____2006) -> term_as_mlty' env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____2012,uu____2013) ->
          term_as_mlty' env t2
      | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
      | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv []
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____2080 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____2080 with
           | (bs1,c1) ->
               let uu____2087 = binders_as_ml_binders env bs1  in
               (match uu____2087 with
                | (mlbs,env1) ->
                    let t_ret =
                      let eff =
                        FStar_TypeChecker_Env.norm_eff_name
                          env1.FStar_Extraction_ML_UEnv.tcenv
                          (FStar_Syntax_Util.comp_effect_name c1)
                         in
                      let uu____2114 =
                        let uu____2121 =
                          FStar_TypeChecker_Env.effect_decl_opt
                            env1.FStar_Extraction_ML_UEnv.tcenv eff
                           in
                        FStar_Util.must uu____2121  in
                      match uu____2114 with
                      | (ed,qualifiers) ->
                          let uu____2142 =
                            FStar_All.pipe_right qualifiers
                              (FStar_List.contains
                                 FStar_Syntax_Syntax.Reifiable)
                             in
                          if uu____2142
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
                    let uu____2149 =
                      FStar_List.fold_right
                        (fun uu____2168  ->
                           fun uu____2169  ->
                             match (uu____2168, uu____2169) with
                             | ((uu____2190,t2),(tag,t')) ->
                                 (FStar_Extraction_ML_Syntax.E_PURE,
                                   (FStar_Extraction_ML_Syntax.MLTY_Fun
                                      (t2, tag, t')))) mlbs (erase1, t_ret)
                       in
                    (match uu____2149 with | (uu____2202,t2) -> t2)))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let res =
            let uu____2227 =
              let uu____2228 = FStar_Syntax_Util.un_uinst head1  in
              uu____2228.FStar_Syntax_Syntax.n  in
            match uu____2227 with
            | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
            | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv args
            | FStar_Syntax_Syntax.Tm_app (head2,args') ->
                let uu____2255 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app
                       (head2, (FStar_List.append args' args)))
                    FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   in
                term_as_mlty' env uu____2255
            | uu____2272 -> FStar_Extraction_ML_UEnv.unknownType  in
          res
      | FStar_Syntax_Syntax.Tm_abs (bs,ty,uu____2275) ->
          let uu____2296 = FStar_Syntax_Subst.open_term bs ty  in
          (match uu____2296 with
           | (bs1,ty1) ->
               let uu____2303 = binders_as_ml_binders env bs1  in
               (match uu____2303 with | (bts,env1) -> term_as_mlty' env1 ty1))
      | FStar_Syntax_Syntax.Tm_type uu____2328 ->
          FStar_Extraction_ML_UEnv.unknownType
      | FStar_Syntax_Syntax.Tm_let uu____2329 ->
          FStar_Extraction_ML_UEnv.unknownType
      | FStar_Syntax_Syntax.Tm_match uu____2342 ->
          FStar_Extraction_ML_UEnv.unknownType

and arg_as_mlty :
  FStar_Extraction_ML_UEnv.env ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 -> FStar_Extraction_ML_Syntax.mlty
  =
  fun g  ->
    fun uu____2366  ->
      match uu____2366 with
      | (a,uu____2372) ->
          let uu____2373 = is_type g a  in
          if uu____2373
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
        let uu____2378 =
          let uu____2391 =
            FStar_TypeChecker_Env.lookup_lid g.FStar_Extraction_ML_UEnv.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____2391 with
          | ((uu____2412,fvty),uu____2414) ->
              let fvty1 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Normalize.UnfoldUntil
                     FStar_Syntax_Syntax.Delta_constant]
                  g.FStar_Extraction_ML_UEnv.tcenv fvty
                 in
              FStar_Syntax_Util.arrow_formals fvty1
           in
        match uu____2378 with
        | (formals,uu____2421) ->
            let mlargs = FStar_List.map (arg_as_mlty g) args  in
            let mlargs1 =
              let n_args = FStar_List.length args  in
              if (FStar_List.length formals) > n_args
              then
                let uu____2465 = FStar_Util.first_N n_args formals  in
                match uu____2465 with
                | (uu____2492,rest) ->
                    let uu____2518 =
                      FStar_List.map
                        (fun uu____2526  ->
                           FStar_Extraction_ML_UEnv.erasedContent) rest
                       in
                    FStar_List.append mlargs uu____2518
              else mlargs  in
            let nm =
              let uu____2533 =
                FStar_Extraction_ML_UEnv.maybe_mangle_type_projector g fv  in
              match uu____2533 with
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
      let uu____2551 =
        FStar_All.pipe_right bs
          (FStar_List.fold_left
             (fun uu____2594  ->
                fun b  ->
                  match uu____2594 with
                  | (ml_bs,env) ->
                      let uu____2634 = is_type_binder g b  in
                      if uu____2634
                      then
                        let b1 = FStar_Pervasives_Native.fst b  in
                        let env1 =
                          FStar_Extraction_ML_UEnv.extend_ty env b1
                            (FStar_Pervasives_Native.Some
                               FStar_Extraction_ML_Syntax.MLTY_Top)
                           in
                        let ml_b =
                          let uu____2652 =
                            FStar_Extraction_ML_UEnv.bv_as_ml_termvar b1  in
                          (uu____2652, FStar_Extraction_ML_Syntax.ml_unit_ty)
                           in
                        ((ml_b :: ml_bs), env1)
                      else
                        (let b1 = FStar_Pervasives_Native.fst b  in
                         let t = term_as_mlty env b1.FStar_Syntax_Syntax.sort
                            in
                         let uu____2666 =
                           FStar_Extraction_ML_UEnv.extend_bv env b1 
                             ([], t) false false false
                            in
                         match uu____2666 with
                         | (env1,b2) ->
                             let ml_b =
                               let uu____2690 =
                                 FStar_Extraction_ML_UEnv.removeTick b2  in
                               (uu____2690, t)  in
                             ((ml_b :: ml_bs), env1))) ([], g))
         in
      match uu____2551 with | (ml_bs,env) -> ((FStar_List.rev ml_bs), env)

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
      | (FStar_Extraction_ML_Syntax.MLE_Seq es1,uu____2758) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (FStar_List.append es1 [e2])
      | (uu____2761,FStar_Extraction_ML_Syntax.MLE_Seq es2) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (e1 :: es2)
      | uu____2765 -> FStar_Extraction_ML_Syntax.MLE_Seq [e1; e2]
  
let mk_MLE_Let :
  Prims.bool ->
    FStar_Extraction_ML_Syntax.mlletbinding ->
      FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr'
  =
  fun top_level  ->
    fun lbs  ->
      fun body  ->
        match lbs with
        | (FStar_Extraction_ML_Syntax.NonRec ,lb::[]) when
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
                    | uu____2793 when
                        (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
                          =
                          FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr
                        -> body.FStar_Extraction_ML_Syntax.expr
                    | uu____2794 ->
                        mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def
                          body)
             | uu____2795 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body))
        | uu____2798 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body)
  
let resugar_pat :
  FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option ->
    FStar_Extraction_ML_Syntax.mlpattern ->
      FStar_Extraction_ML_Syntax.mlpattern
  =
  fun q  ->
    fun p  ->
      match p with
      | FStar_Extraction_ML_Syntax.MLP_CTor (d,pats) ->
          let uu____2815 = FStar_Extraction_ML_Util.is_xtuple d  in
          (match uu____2815 with
           | FStar_Pervasives_Native.Some n1 ->
               FStar_Extraction_ML_Syntax.MLP_Tuple pats
           | uu____2819 ->
               (match q with
                | FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Record_ctor (ty,fns)) ->
                    let path =
                      FStar_List.map FStar_Ident.text_of_id ty.FStar_Ident.ns
                       in
                    let fs = record_fields fns pats  in
                    FStar_Extraction_ML_Syntax.MLP_Record (path, fs)
                | uu____2846 -> p))
      | uu____2849 -> p
  
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
                       (fun uu____2929  ->
                          let uu____2930 =
                            FStar_Extraction_ML_Code.string_of_mlty
                              g.FStar_Extraction_ML_UEnv.currentModule t'
                             in
                          let uu____2931 =
                            FStar_Extraction_ML_Code.string_of_mlty
                              g.FStar_Extraction_ML_UEnv.currentModule t
                             in
                          FStar_Util.print2
                            "Expected pattern type %s; got pattern type %s\n"
                            uu____2930 uu____2931)
                   else ();
                   ok)
               in
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int
                (c,swopt)) when
                let uu____2961 = FStar_Options.codegen ()  in
                uu____2961 <> (FStar_Pervasives_Native.Some "Kremlin") ->
                let uu____2966 =
                  match swopt with
                  | FStar_Pervasives_Native.None  ->
                      let uu____2979 =
                        let uu____2980 =
                          let uu____2981 =
                            FStar_Extraction_ML_Util.mlconst_of_const
                              p.FStar_Syntax_Syntax.p
                              (FStar_Const.Const_int
                                 (c, FStar_Pervasives_Native.None))
                             in
                          FStar_Extraction_ML_Syntax.MLE_Const uu____2981  in
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.ml_int_ty) uu____2980
                         in
                      (uu____2979, FStar_Extraction_ML_Syntax.ml_int_ty)
                  | FStar_Pervasives_Native.Some sw ->
                      let source_term =
                        FStar_ToSyntax_ToSyntax.desugar_machine_integer
                          (g.FStar_Extraction_ML_UEnv.tcenv).FStar_TypeChecker_Env.dsenv
                          c sw FStar_Range.dummyRange
                         in
                      let uu____3002 = term_as_mlexpr g source_term  in
                      (match uu____3002 with
                       | (mlterm,uu____3014,mlty) -> (mlterm, mlty))
                   in
                (match uu____2966 with
                 | (mlc,ml_ty) ->
                     let x = FStar_Extraction_ML_Syntax.gensym ()  in
                     let when_clause =
                       let uu____3034 =
                         let uu____3035 =
                           let uu____3042 =
                             let uu____3045 =
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty ml_ty)
                                 (FStar_Extraction_ML_Syntax.MLE_Var x)
                                in
                             [uu____3045; mlc]  in
                           (FStar_Extraction_ML_Util.prims_op_equality,
                             uu____3042)
                            in
                         FStar_Extraction_ML_Syntax.MLE_App uu____3035  in
                       FStar_All.pipe_left
                         (FStar_Extraction_ML_Syntax.with_ty
                            FStar_Extraction_ML_Syntax.ml_bool_ty) uu____3034
                        in
                     let uu____3048 = ok ml_ty  in
                     (g,
                       (FStar_Pervasives_Native.Some
                          ((FStar_Extraction_ML_Syntax.MLP_Var x),
                            [when_clause])), uu____3048))
            | FStar_Syntax_Syntax.Pat_constant s ->
                let t =
                  FStar_TypeChecker_TcTerm.tc_constant
                    g.FStar_Extraction_ML_UEnv.tcenv FStar_Range.dummyRange s
                   in
                let mlty = term_as_mlty g t  in
                let uu____3068 =
                  let uu____3077 =
                    let uu____3084 =
                      let uu____3085 =
                        FStar_Extraction_ML_Util.mlconst_of_const
                          p.FStar_Syntax_Syntax.p s
                         in
                      FStar_Extraction_ML_Syntax.MLP_Const uu____3085  in
                    (uu____3084, [])  in
                  FStar_Pervasives_Native.Some uu____3077  in
                let uu____3094 = ok mlty  in (g, uu____3068, uu____3094)
            | FStar_Syntax_Syntax.Pat_var x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort  in
                let uu____3105 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp
                   in
                (match uu____3105 with
                 | (g1,x1) ->
                     let uu____3128 = ok mlty  in
                     (g1,
                       (if imp
                        then FStar_Pervasives_Native.None
                        else
                          FStar_Pervasives_Native.Some
                            ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                       uu____3128))
            | FStar_Syntax_Syntax.Pat_wild x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort  in
                let uu____3162 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp
                   in
                (match uu____3162 with
                 | (g1,x1) ->
                     let uu____3185 = ok mlty  in
                     (g1,
                       (if imp
                        then FStar_Pervasives_Native.None
                        else
                          FStar_Pervasives_Native.Some
                            ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                       uu____3185))
            | FStar_Syntax_Syntax.Pat_dot_term uu____3217 ->
                (g, FStar_Pervasives_Native.None, true)
            | FStar_Syntax_Syntax.Pat_cons (f,pats) ->
                let uu____3256 =
                  let uu____3261 = FStar_Extraction_ML_UEnv.lookup_fv g f  in
                  match uu____3261 with
                  | FStar_Util.Inr
                      (uu____3266,{
                                    FStar_Extraction_ML_Syntax.expr =
                                      FStar_Extraction_ML_Syntax.MLE_Name n1;
                                    FStar_Extraction_ML_Syntax.mlty =
                                      uu____3268;
                                    FStar_Extraction_ML_Syntax.loc =
                                      uu____3269;_},ttys,uu____3271)
                      -> (n1, ttys)
                  | uu____3284 -> failwith "Expected a constructor"  in
                (match uu____3256 with
                 | (d,tys) ->
                     let nTyVars =
                       FStar_List.length (FStar_Pervasives_Native.fst tys)
                        in
                     let uu____3306 = FStar_Util.first_N nTyVars pats  in
                     (match uu____3306 with
                      | (tysVarPats,restPats) ->
                          let f_ty_opt =
                            try
                              let mlty_args =
                                FStar_All.pipe_right tysVarPats
                                  (FStar_List.map
                                     (fun uu____3439  ->
                                        match uu____3439 with
                                        | (p1,uu____3447) ->
                                            (match p1.FStar_Syntax_Syntax.v
                                             with
                                             | FStar_Syntax_Syntax.Pat_dot_term
                                                 (uu____3452,t) ->
                                                 term_as_mlty g t
                                             | uu____3458 ->
                                                 (FStar_Extraction_ML_UEnv.debug
                                                    g
                                                    (fun uu____3462  ->
                                                       let uu____3463 =
                                                         FStar_Syntax_Print.pat_to_string
                                                           p1
                                                          in
                                                       FStar_Util.print1
                                                         "Pattern %s is not extractable"
                                                         uu____3463);
                                                  FStar_Exn.raise
                                                    Un_extractable))))
                                 in
                              let f_ty =
                                FStar_Extraction_ML_Util.subst tys mlty_args
                                 in
                              let uu____3465 =
                                FStar_Extraction_ML_Util.uncurry_mlty_fun
                                  f_ty
                                 in
                              FStar_Pervasives_Native.Some uu____3465
                            with
                            | Un_extractable  -> FStar_Pervasives_Native.None
                             in
                          let uu____3494 =
                            FStar_Util.fold_map
                              (fun g1  ->
                                 fun uu____3530  ->
                                   match uu____3530 with
                                   | (p1,imp1) ->
                                       let uu____3549 =
                                         extract_one_pat true g1 p1
                                           FStar_Pervasives_Native.None
                                           term_as_mlexpr
                                          in
                                       (match uu____3549 with
                                        | (g2,p2,uu____3578) -> (g2, p2))) g
                              tysVarPats
                             in
                          (match uu____3494 with
                           | (g1,tyMLPats) ->
                               let uu____3639 =
                                 FStar_Util.fold_map
                                   (fun uu____3703  ->
                                      fun uu____3704  ->
                                        match (uu____3703, uu____3704) with
                                        | ((g2,f_ty_opt1),(p1,imp1)) ->
                                            let uu____3797 =
                                              match f_ty_opt1 with
                                              | FStar_Pervasives_Native.Some
                                                  (hd1::rest,res) ->
                                                  ((FStar_Pervasives_Native.Some
                                                      (rest, res)),
                                                    (FStar_Pervasives_Native.Some
                                                       hd1))
                                              | uu____3857 ->
                                                  (FStar_Pervasives_Native.None,
                                                    FStar_Pervasives_Native.None)
                                               in
                                            (match uu____3797 with
                                             | (f_ty_opt2,expected_ty) ->
                                                 let uu____3928 =
                                                   extract_one_pat false g2
                                                     p1 expected_ty
                                                     term_as_mlexpr
                                                    in
                                                 (match uu____3928 with
                                                  | (g3,p2,uu____3969) ->
                                                      ((g3, f_ty_opt2), p2))))
                                   (g1, f_ty_opt) restPats
                                  in
                               (match uu____3639 with
                                | ((g2,f_ty_opt1),restMLPats) ->
                                    let uu____4087 =
                                      let uu____4098 =
                                        FStar_All.pipe_right
                                          (FStar_List.append tyMLPats
                                             restMLPats)
                                          (FStar_List.collect
                                             (fun uu___60_4149  ->
                                                match uu___60_4149 with
                                                | FStar_Pervasives_Native.Some
                                                    x -> [x]
                                                | uu____4191 -> []))
                                         in
                                      FStar_All.pipe_right uu____4098
                                        FStar_List.split
                                       in
                                    (match uu____4087 with
                                     | (mlPats,when_clauses) ->
                                         let pat_ty_compat =
                                           match f_ty_opt1 with
                                           | FStar_Pervasives_Native.Some
                                               ([],t) -> ok t
                                           | uu____4264 -> false  in
                                         let uu____4273 =
                                           let uu____4282 =
                                             let uu____4289 =
                                               resugar_pat
                                                 f.FStar_Syntax_Syntax.fv_qual
                                                 (FStar_Extraction_ML_Syntax.MLP_CTor
                                                    (d, mlPats))
                                                in
                                             let uu____4292 =
                                               FStar_All.pipe_right
                                                 when_clauses
                                                 FStar_List.flatten
                                                in
                                             (uu____4289, uu____4292)  in
                                           FStar_Pervasives_Native.Some
                                             uu____4282
                                            in
                                         (g2, uu____4273, pat_ty_compat))))))
  
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
            let uu____4405 =
              extract_one_pat false g1 p1 expected_t1 term_as_mlexpr  in
            match uu____4405 with
            | (g2,FStar_Pervasives_Native.Some (x,v1),b) -> (g2, (x, v1), b)
            | uu____4462 ->
                failwith "Impossible: Unable to translate pattern"
             in
          let mk_when_clause whens =
            match whens with
            | [] -> FStar_Pervasives_Native.None
            | hd1::tl1 ->
                let uu____4505 =
                  FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd1
                    tl1
                   in
                FStar_Pervasives_Native.Some uu____4505
             in
          let uu____4506 =
            extract_one_pat1 g p (FStar_Pervasives_Native.Some expected_t)
             in
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
            | FStar_Extraction_ML_Syntax.MLTY_Fun (t0,uu____4644,t1) ->
                let x = FStar_Extraction_ML_Syntax.gensym ()  in
                let uu____4647 =
                  let uu____4658 =
                    let uu____4667 =
                      FStar_All.pipe_left
                        (FStar_Extraction_ML_Syntax.with_ty t0)
                        (FStar_Extraction_ML_Syntax.MLE_Var x)
                       in
                    ((x, t0), uu____4667)  in
                  uu____4658 :: more_args  in
                eta_args uu____4647 t1
            | FStar_Extraction_ML_Syntax.MLTY_Named (uu____4680,uu____4681)
                -> ((FStar_List.rev more_args), t)
            | uu____4704 -> failwith "Impossible: Head type is not an arrow"
             in
          let as_record qual1 e =
            match ((e.FStar_Extraction_ML_Syntax.expr), qual1) with
            | (FStar_Extraction_ML_Syntax.MLE_CTor
               (uu____4732,args),FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Record_ctor (tyname,fields))) ->
                let path =
                  FStar_List.map FStar_Ident.text_of_id tyname.FStar_Ident.ns
                   in
                let fields1 = record_fields fields args  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     e.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_Record (path, fields1))
            | uu____4764 -> e  in
          let resugar_and_maybe_eta qual1 e =
            let uu____4782 = eta_args [] residualType  in
            match uu____4782 with
            | (eargs,tres) ->
                (match eargs with
                 | [] ->
                     let uu____4835 = as_record qual1 e  in
                     FStar_Extraction_ML_Util.resugar_exp uu____4835
                 | uu____4836 ->
                     let uu____4847 = FStar_List.unzip eargs  in
                     (match uu____4847 with
                      | (binders,eargs1) ->
                          (match e.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_CTor (head1,args)
                               ->
                               let body =
                                 let uu____4889 =
                                   let uu____4890 =
                                     FStar_All.pipe_left
                                       (FStar_Extraction_ML_Syntax.with_ty
                                          tres)
                                       (FStar_Extraction_ML_Syntax.MLE_CTor
                                          (head1,
                                            (FStar_List.append args eargs1)))
                                      in
                                   FStar_All.pipe_left (as_record qual1)
                                     uu____4890
                                    in
                                 FStar_All.pipe_left
                                   FStar_Extraction_ML_Util.resugar_exp
                                   uu____4889
                                  in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    e.FStar_Extraction_ML_Syntax.mlty)
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    (binders, body))
                           | uu____4899 ->
                               failwith "Impossible: Not a constructor")))
             in
          match ((mlAppExpr.FStar_Extraction_ML_Syntax.expr), qual) with
          | (uu____4902,FStar_Pervasives_Native.None ) -> mlAppExpr
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____4906;
                FStar_Extraction_ML_Syntax.loc = uu____4907;_},mle::args),FStar_Pervasives_Native.Some
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
                | uu____4934 ->
                    let uu____4937 =
                      let uu____4944 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj
                         in
                      (uu____4944, args)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____4937
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
                     FStar_Extraction_ML_Syntax.mlty = uu____4948;
                     FStar_Extraction_ML_Syntax.loc = uu____4949;_},uu____4950);
                FStar_Extraction_ML_Syntax.mlty = uu____4951;
                FStar_Extraction_ML_Syntax.loc = uu____4952;_},mle::args),FStar_Pervasives_Native.Some
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
                | uu____4983 ->
                    let uu____4986 =
                      let uu____4993 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj
                         in
                      (uu____4993, args)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____4986
                 in
              FStar_Extraction_ML_Syntax.with_ty
                mlAppExpr.FStar_Extraction_ML_Syntax.mlty e
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____4997;
                FStar_Extraction_ML_Syntax.loc = uu____4998;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____5006 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5006
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____5010;
                FStar_Extraction_ML_Syntax.loc = uu____5011;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____5013)) ->
              let uu____5026 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5026
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____5030;
                     FStar_Extraction_ML_Syntax.loc = uu____5031;_},uu____5032);
                FStar_Extraction_ML_Syntax.mlty = uu____5033;
                FStar_Extraction_ML_Syntax.loc = uu____5034;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____5046 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5046
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____5050;
                     FStar_Extraction_ML_Syntax.loc = uu____5051;_},uu____5052);
                FStar_Extraction_ML_Syntax.mlty = uu____5053;
                FStar_Extraction_ML_Syntax.loc = uu____5054;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____5056)) ->
              let uu____5073 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5073
          | (FStar_Extraction_ML_Syntax.MLE_Name
             mlp,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor
             )) ->
              let uu____5079 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5079
          | (FStar_Extraction_ML_Syntax.MLE_Name
             mlp,FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____5083)) ->
              let uu____5092 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5092
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____5096;
                FStar_Extraction_ML_Syntax.loc = uu____5097;_},uu____5098),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____5105 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5105
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____5109;
                FStar_Extraction_ML_Syntax.loc = uu____5110;_},uu____5111),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____5112)) ->
              let uu____5125 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5125
          | uu____5128 -> mlAppExpr
  
let maybe_downgrade_eff :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.e_tag ->
      FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.e_tag
  =
  fun g  ->
    fun f  ->
      fun t  ->
        let uu____5144 =
          (f = FStar_Extraction_ML_Syntax.E_GHOST) &&
            (type_leq g t FStar_Extraction_ML_Syntax.ml_unit_ty)
           in
        if uu____5144 then FStar_Extraction_ML_Syntax.E_PURE else f
  
let rec term_as_mlexpr :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Extraction_ML_Syntax.mlexpr,FStar_Extraction_ML_Syntax.e_tag,
        FStar_Extraction_ML_Syntax.mlty) FStar_Pervasives_Native.tuple3
  =
  fun g  ->
    fun t  ->
      let uu____5198 = term_as_mlexpr' g t  in
      match uu____5198 with
      | (e,tag,ty) ->
          let tag1 = maybe_downgrade_eff g tag ty  in
          (FStar_Extraction_ML_UEnv.debug g
             (fun u  ->
                let uu____5219 =
                  let uu____5220 = FStar_Syntax_Print.tag_of_term t  in
                  let uu____5221 = FStar_Syntax_Print.term_to_string t  in
                  let uu____5222 =
                    FStar_Extraction_ML_Code.string_of_mlty
                      g.FStar_Extraction_ML_UEnv.currentModule ty
                     in
                  FStar_Util.format4
                    "term_as_mlexpr (%s) :  %s has ML type %s and effect %s\n"
                    uu____5220 uu____5221 uu____5222
                    (FStar_Extraction_ML_Util.eff_to_string tag1)
                   in
                FStar_Util.print_string uu____5219);
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
          let uu____5231 = check_term_as_mlexpr' g t f ty  in
          match uu____5231 with
          | (e,t1) ->
              let uu____5242 = erase g e t1 f  in
              (match uu____5242 with | (r,uu____5254,t2) -> (r, t2))

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
          let uu____5264 = term_as_mlexpr g e0  in
          match uu____5264 with
          | (e,tag,t) ->
              let tag1 = maybe_downgrade_eff g tag t  in
              if FStar_Extraction_ML_Util.eff_leq tag1 f
              then
                let uu____5283 = maybe_coerce g e t ty  in (uu____5283, ty)
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
           let uu____5301 =
             let uu____5302 =
               FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos  in
             let uu____5303 = FStar_Syntax_Print.tag_of_term top  in
             let uu____5304 = FStar_Syntax_Print.term_to_string top  in
             FStar_Util.format3 "%s: term_as_mlexpr' (%s) :  %s \n"
               uu____5302 uu____5303 uu____5304
              in
           FStar_Util.print_string uu____5301);
      (let t = FStar_Syntax_Subst.compress top  in
       match t.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____5312 =
             let uu____5313 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5313
              in
           failwith uu____5312
       | FStar_Syntax_Syntax.Tm_delayed uu____5320 ->
           let uu____5345 =
             let uu____5346 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5346
              in
           failwith uu____5345
       | FStar_Syntax_Syntax.Tm_uvar uu____5353 ->
           let uu____5370 =
             let uu____5371 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5371
              in
           failwith uu____5370
       | FStar_Syntax_Syntax.Tm_bvar uu____5378 ->
           let uu____5379 =
             let uu____5380 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5380
              in
           failwith uu____5379
       | FStar_Syntax_Syntax.Tm_type uu____5387 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_refine uu____5388 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_arrow uu____5395 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Mutable_alloc ))
           ->
           FStar_Errors.raise_err
             (FStar_Errors.Error_NoLetMutable,
               "let-mutable no longer supported")
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_monadic (m,uu____5421)) ->
           let t2 = FStar_Syntax_Subst.compress t1  in
           (match t2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) when
                FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname ->
                let uu____5451 =
                  let uu____5458 =
                    FStar_TypeChecker_Env.effect_decl_opt
                      g.FStar_Extraction_ML_UEnv.tcenv m
                     in
                  FStar_Util.must uu____5458  in
                (match uu____5451 with
                 | (ed,qualifiers) ->
                     let uu____5485 =
                       let uu____5486 =
                         FStar_All.pipe_right qualifiers
                           (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                          in
                       FStar_All.pipe_right uu____5486 Prims.op_Negation  in
                     if uu____5485
                     then term_as_mlexpr' g t2
                     else
                       failwith
                         "This should not happen (should have been handled at Tm_abs level)")
            | uu____5502 -> term_as_mlexpr' g t2)
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____5504) -> term_as_mlexpr' g t1
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____5510) -> term_as_mlexpr' g t1
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____5516 =
             FStar_TypeChecker_TcTerm.type_of_tot_term
               g.FStar_Extraction_ML_UEnv.tcenv t
              in
           (match uu____5516 with
            | (uu____5529,ty,uu____5531) ->
                let ml_ty = term_as_mlty g ty  in
                let uu____5533 =
                  let uu____5534 =
                    FStar_Extraction_ML_Util.mlexpr_of_const
                      t.FStar_Syntax_Syntax.pos c
                     in
                  FStar_Extraction_ML_Syntax.with_ty ml_ty uu____5534  in
                (uu____5533, FStar_Extraction_ML_Syntax.E_PURE, ml_ty))
       | FStar_Syntax_Syntax.Tm_name uu____5535 ->
           let uu____5536 = is_type g t  in
           if uu____5536
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____5544 = FStar_Extraction_ML_UEnv.lookup_term g t  in
              match uu____5544 with
              | (FStar_Util.Inl uu____5557,uu____5558) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | (FStar_Util.Inr (uu____5595,x,mltys,uu____5598),qual) ->
                  (match mltys with
                   | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                       ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | ([],t1) ->
                       let uu____5644 =
                         maybe_eta_data_and_project_record g qual t1 x  in
                       (uu____5644, FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | uu____5645 -> err_uninst g t mltys t))
       | FStar_Syntax_Syntax.Tm_fvar uu____5652 ->
           let uu____5653 = is_type g t  in
           if uu____5653
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____5661 = FStar_Extraction_ML_UEnv.lookup_term g t  in
              match uu____5661 with
              | (FStar_Util.Inl uu____5674,uu____5675) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | (FStar_Util.Inr (uu____5712,x,mltys,uu____5715),qual) ->
                  (match mltys with
                   | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                       ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | ([],t1) ->
                       let uu____5761 =
                         maybe_eta_data_and_project_record g qual t1 x  in
                       (uu____5761, FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | uu____5762 -> err_uninst g t mltys t))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,copt) ->
           let uu____5792 = FStar_Syntax_Subst.open_term bs body  in
           (match uu____5792 with
            | (bs1,body1) ->
                let uu____5805 = binders_as_ml_binders g bs1  in
                (match uu____5805 with
                 | (ml_bs,env) ->
                     let body2 =
                       match copt with
                       | FStar_Pervasives_Native.Some c ->
                           let uu____5838 =
                             FStar_TypeChecker_Env.is_reifiable
                               env.FStar_Extraction_ML_UEnv.tcenv c
                              in
                           if uu____5838
                           then
                             FStar_TypeChecker_Util.reify_body
                               env.FStar_Extraction_ML_UEnv.tcenv body1
                           else body1
                       | FStar_Pervasives_Native.None  ->
                           (FStar_Extraction_ML_UEnv.debug g
                              (fun uu____5843  ->
                                 let uu____5844 =
                                   FStar_Syntax_Print.term_to_string body1
                                    in
                                 FStar_Util.print1
                                   "No computation type for: %s\n" uu____5844);
                            body1)
                        in
                     let uu____5845 = term_as_mlexpr env body2  in
                     (match uu____5845 with
                      | (ml_body,f,t1) ->
                          let uu____5861 =
                            FStar_List.fold_right
                              (fun uu____5880  ->
                                 fun uu____5881  ->
                                   match (uu____5880, uu____5881) with
                                   | ((uu____5902,targ),(f1,t2)) ->
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         (FStar_Extraction_ML_Syntax.MLTY_Fun
                                            (targ, f1, t2)))) ml_bs (f, t1)
                             in
                          (match uu____5861 with
                           | (f1,tfun) ->
                               let uu____5922 =
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty tfun)
                                   (FStar_Extraction_ML_Syntax.MLE_Fun
                                      (ml_bs, ml_body))
                                  in
                               (uu____5922, f1, tfun)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____5929;
              FStar_Syntax_Syntax.vars = uu____5930;_},(a1,uu____5932)::[])
           ->
           let ty =
             let uu____5962 =
               FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid  in
             term_as_mlty g uu____5962  in
           let uu____5963 =
             let uu____5964 =
               FStar_Extraction_ML_Util.mlexpr_of_range
                 a1.FStar_Syntax_Syntax.pos
                in
             FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty)
               uu____5964
              in
           (uu____5963, FStar_Extraction_ML_Syntax.E_PURE, ty)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____5965;
              FStar_Syntax_Syntax.vars = uu____5966;_},(a1,uu____5968)::
            (a2,uu____5970)::[])
           -> term_as_mlexpr' g a1
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____6009);
              FStar_Syntax_Syntax.pos = uu____6010;
              FStar_Syntax_Syntax.vars = uu____6011;_},uu____6012)
           -> failwith "Unreachable? Tm_app Const_reflect"
       | FStar_Syntax_Syntax.Tm_app (head1,uu____6040::(v1,uu____6042)::[])
           when (FStar_Syntax_Util.is_fstar_tactics_embed head1) && false ->
           let uu____6083 =
             let uu____6086 = FStar_Syntax_Print.term_to_string v1  in
             FStar_Util.format2 "Trying to extract a quotation of %s"
               uu____6086
              in
           let s =
             let uu____6088 =
               let uu____6089 =
                 let uu____6090 =
                   let uu____6093 = FStar_Util.marshal v1  in
                   FStar_Util.bytes_of_string uu____6093  in
                 FStar_Extraction_ML_Syntax.MLC_Bytes uu____6090  in
               FStar_Extraction_ML_Syntax.MLE_Const uu____6089  in
             FStar_Extraction_ML_Syntax.with_ty
               FStar_Extraction_ML_Syntax.ml_string_ty uu____6088
              in
           let zero1 =
             FStar_Extraction_ML_Syntax.with_ty
               FStar_Extraction_ML_Syntax.ml_int_ty
               (FStar_Extraction_ML_Syntax.MLE_Const
                  (FStar_Extraction_ML_Syntax.MLC_Int
                     ("0", FStar_Pervasives_Native.None)))
              in
           let term_ty =
             let uu____6108 =
               FStar_Syntax_Syntax.fvar
                 FStar_Parser_Const.fstar_syntax_syntax_term
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None
                in
             term_as_mlty g uu____6108  in
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
           let uu____6113 =
             FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty term_ty)
               (FStar_Extraction_ML_Syntax.MLE_App
                  (marshal_from_string, [s; zero1]))
              in
           (uu____6113, FStar_Extraction_ML_Syntax.E_PURE, term_ty)
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let is_total rc =
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_Tot_lid)
               ||
               (FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
                  (FStar_List.existsb
                     (fun uu___61_6145  ->
                        match uu___61_6145 with
                        | FStar_Syntax_Syntax.TOTAL  -> true
                        | uu____6146 -> false)))
              in
           let uu____6147 =
             let uu____6152 =
               let uu____6153 = FStar_Syntax_Subst.compress head1  in
               uu____6153.FStar_Syntax_Syntax.n  in
             ((head1.FStar_Syntax_Syntax.n), uu____6152)  in
           (match uu____6147 with
            | (FStar_Syntax_Syntax.Tm_uvar uu____6162,uu____6163) ->
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
            | (uu____6181,FStar_Syntax_Syntax.Tm_abs
               (bs,uu____6183,FStar_Pervasives_Native.Some rc)) when
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
            | (uu____6204,FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_reify )) ->
                let e =
                  let uu____6206 = FStar_List.hd args  in
                  FStar_TypeChecker_Util.reify_body_with_arg
                    g.FStar_Extraction_ML_UEnv.tcenv head1 uu____6206
                   in
                let tm =
                  let uu____6216 =
                    let uu____6217 = FStar_TypeChecker_Util.remove_reify e
                       in
                    let uu____6218 = FStar_List.tl args  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____6217 uu____6218  in
                  uu____6216 FStar_Pervasives_Native.None
                    t.FStar_Syntax_Syntax.pos
                   in
                term_as_mlexpr' g tm
            | uu____6227 ->
                let rec extract_app is_data uu____6272 uu____6273 restArgs =
                  match (uu____6272, uu____6273) with
                  | ((mlhead,mlargs_f),(f,t1)) ->
                      (match (restArgs, t1) with
                       | ([],uu____6363) ->
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
                                | uu____6385 -> false)
                              in
                           let uu____6386 =
                             if evaluation_order_guaranteed
                             then
                               let uu____6411 =
                                 FStar_All.pipe_right
                                   (FStar_List.rev mlargs_f)
                                   (FStar_List.map
                                      FStar_Pervasives_Native.fst)
                                  in
                               ([], uu____6411)
                             else
                               FStar_List.fold_left
                                 (fun uu____6465  ->
                                    fun uu____6466  ->
                                      match (uu____6465, uu____6466) with
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
                                             let uu____6569 =
                                               let uu____6572 =
                                                 FStar_All.pipe_left
                                                   (FStar_Extraction_ML_Syntax.with_ty
                                                      arg.FStar_Extraction_ML_Syntax.mlty)
                                                   (FStar_Extraction_ML_Syntax.MLE_Var
                                                      x)
                                                  in
                                               uu____6572 :: out_args  in
                                             (((x, arg) :: lbs), uu____6569)))
                                 ([], []) mlargs_f
                              in
                           (match uu____6386 with
                            | (lbs,mlargs) ->
                                let app =
                                  let uu____6622 =
                                    FStar_All.pipe_left
                                      (FStar_Extraction_ML_Syntax.with_ty t1)
                                      (FStar_Extraction_ML_Syntax.MLE_App
                                         (mlhead, mlargs))
                                     in
                                  FStar_All.pipe_left
                                    (maybe_eta_data_and_project_record g
                                       is_data t1) uu____6622
                                   in
                                let l_app =
                                  FStar_List.fold_right
                                    (fun uu____6634  ->
                                       fun out  ->
                                         match uu____6634 with
                                         | (x,arg) ->
                                             FStar_All.pipe_left
                                               (FStar_Extraction_ML_Syntax.with_ty
                                                  out.FStar_Extraction_ML_Syntax.mlty)
                                               (mk_MLE_Let false
                                                  (FStar_Extraction_ML_Syntax.NonRec,
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
                                                       FStar_Extraction_ML_Syntax.mllb_meta
                                                         = [];
                                                       FStar_Extraction_ML_Syntax.print_typ
                                                         = true
                                                     }]) out)) lbs app
                                   in
                                (l_app, f, t1))
                       | ((arg,uu____6653)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                          (formal_t,f',t2)) when
                           (is_type g arg) &&
                             (type_leq g formal_t
                                FStar_Extraction_ML_Syntax.ml_unit_ty)
                           ->
                           let uu____6684 =
                             let uu____6689 =
                               FStar_Extraction_ML_Util.join
                                 arg.FStar_Syntax_Syntax.pos f f'
                                in
                             (uu____6689, t2)  in
                           extract_app is_data
                             (mlhead,
                               ((FStar_Extraction_ML_Syntax.ml_unit,
                                  FStar_Extraction_ML_Syntax.E_PURE) ::
                               mlargs_f)) uu____6684 rest
                       | ((e0,uu____6701)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                          (tExpected,f',t2)) ->
                           let r = e0.FStar_Syntax_Syntax.pos  in
                           let uu____6733 = term_as_mlexpr g e0  in
                           (match uu____6733 with
                            | (e01,f0,tInferred) ->
                                let e02 =
                                  maybe_coerce g e01 tInferred tExpected  in
                                let uu____6750 =
                                  let uu____6755 =
                                    FStar_Extraction_ML_Util.join_l r
                                      [f; f'; f0]
                                     in
                                  (uu____6755, t2)  in
                                extract_app is_data
                                  (mlhead, ((e02, f0) :: mlargs_f))
                                  uu____6750 rest)
                       | uu____6766 ->
                           let uu____6779 =
                             FStar_Extraction_ML_Util.udelta_unfold g t1  in
                           (match uu____6779 with
                            | FStar_Pervasives_Native.Some t2 ->
                                extract_app is_data (mlhead, mlargs_f)
                                  (f, t2) restArgs
                            | FStar_Pervasives_Native.None  ->
                                err_ill_typed_application g top restArgs t1))
                   in
                let extract_app_maybe_projector is_data mlhead uu____6836
                  args1 =
                  match uu____6836 with
                  | (f,t1) ->
                      (match is_data with
                       | FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_projector uu____6868)
                           ->
                           let rec remove_implicits args2 f1 t2 =
                             match (args2, t2) with
                             | ((a0,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____6946))::args3,FStar_Extraction_ML_Syntax.MLTY_Fun
                                (uu____6948,f',t3)) ->
                                 let uu____6985 =
                                   FStar_Extraction_ML_Util.join
                                     a0.FStar_Syntax_Syntax.pos f1 f'
                                    in
                                 remove_implicits args3 uu____6985 t3
                             | uu____6986 -> (args2, f1, t2)  in
                           let uu____7011 = remove_implicits args1 f t1  in
                           (match uu____7011 with
                            | (args2,f1,t2) ->
                                extract_app is_data (mlhead, []) (f1, t2)
                                  args2)
                       | uu____7067 ->
                           extract_app is_data (mlhead, []) (f, t1) args1)
                   in
                let uu____7080 = is_type g t  in
                if uu____7080
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
                         (let uu____7097 =
                            let uu____7098 =
                              FStar_Extraction_ML_Syntax.string_of_mlpath
                                g.FStar_Extraction_ML_UEnv.currentModule
                               in
                            uu____7098 = "FStar.Tactics.Builtins"  in
                          Prims.op_Negation uu____7097)
                       ->
                       (match args with
                        | a::b::[] ->
                            term_as_mlexpr g (FStar_Pervasives_Native.fst a)
                        | uu____7139 ->
                            let uu____7148 =
                              FStar_Syntax_Print.args_to_string args  in
                            failwith uu____7148)
                   | FStar_Syntax_Syntax.Tm_name uu____7155 ->
                       let uu____7156 =
                         let uu____7169 =
                           FStar_Extraction_ML_UEnv.lookup_term g head2  in
                         match uu____7169 with
                         | (FStar_Util.Inr (uu____7188,x1,x2,x3),q) ->
                             ((x1, x2, x3), q)
                         | uu____7233 -> failwith "FIXME Ty"  in
                       (match uu____7156 with
                        | ((head_ml,(vars,t1),inst_ok),qual) ->
                            let has_typ_apps =
                              match args with
                              | (a,uu____7283)::uu____7284 -> is_type g a
                              | uu____7303 -> false  in
                            let uu____7312 =
                              match vars with
                              | uu____7341::uu____7342 when
                                  (Prims.op_Negation has_typ_apps) && inst_ok
                                  -> (head_ml, t1, args)
                              | uu____7353 ->
                                  let n1 = FStar_List.length vars  in
                                  if n1 <= (FStar_List.length args)
                                  then
                                    let uu____7381 =
                                      FStar_Util.first_N n1 args  in
                                    (match uu____7381 with
                                     | (prefix1,rest) ->
                                         let prefixAsMLTypes =
                                           FStar_List.map
                                             (fun uu____7470  ->
                                                match uu____7470 with
                                                | (x,uu____7476) ->
                                                    term_as_mlty g x) prefix1
                                            in
                                         let t2 =
                                           instantiate (vars, t1)
                                             prefixAsMLTypes
                                            in
                                         let mk_tapp e ty_args =
                                           match ty_args with
                                           | [] -> e
                                           | uu____7489 ->
                                               let uu___65_7492 = e  in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (FStar_Extraction_ML_Syntax.MLE_TApp
                                                      (e, ty_args));
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   =
                                                   (uu___65_7492.FStar_Extraction_ML_Syntax.mlty);
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___65_7492.FStar_Extraction_ML_Syntax.loc)
                                               }
                                            in
                                         let head3 =
                                           match head_ml.FStar_Extraction_ML_Syntax.expr
                                           with
                                           | FStar_Extraction_ML_Syntax.MLE_Name
                                               uu____7496 ->
                                               let uu___66_7497 =
                                                 mk_tapp head_ml
                                                   prefixAsMLTypes
                                                  in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (uu___66_7497.FStar_Extraction_ML_Syntax.expr);
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   = t2;
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___66_7497.FStar_Extraction_ML_Syntax.loc)
                                               }
                                           | FStar_Extraction_ML_Syntax.MLE_Var
                                               uu____7498 ->
                                               let uu___66_7499 =
                                                 mk_tapp head_ml
                                                   prefixAsMLTypes
                                                  in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (uu___66_7499.FStar_Extraction_ML_Syntax.expr);
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   = t2;
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___66_7499.FStar_Extraction_ML_Syntax.loc)
                                               }
                                           | FStar_Extraction_ML_Syntax.MLE_App
                                               (head3,{
                                                        FStar_Extraction_ML_Syntax.expr
                                                          =
                                                          FStar_Extraction_ML_Syntax.MLE_Const
                                                          (FStar_Extraction_ML_Syntax.MLC_Unit
                                                          );
                                                        FStar_Extraction_ML_Syntax.mlty
                                                          = uu____7501;
                                                        FStar_Extraction_ML_Syntax.loc
                                                          = uu____7502;_}::[])
                                               ->
                                               FStar_All.pipe_right
                                                 (FStar_Extraction_ML_Syntax.MLE_App
                                                    ((let uu___67_7508 =
                                                        mk_tapp head3
                                                          prefixAsMLTypes
                                                         in
                                                      {
                                                        FStar_Extraction_ML_Syntax.expr
                                                          =
                                                          (uu___67_7508.FStar_Extraction_ML_Syntax.expr);
                                                        FStar_Extraction_ML_Syntax.mlty
                                                          =
                                                          (FStar_Extraction_ML_Syntax.MLTY_Fun
                                                             (FStar_Extraction_ML_Syntax.ml_unit_ty,
                                                               FStar_Extraction_ML_Syntax.E_PURE,
                                                               t2));
                                                        FStar_Extraction_ML_Syntax.loc
                                                          =
                                                          (uu___67_7508.FStar_Extraction_ML_Syntax.loc)
                                                      }),
                                                      [FStar_Extraction_ML_Syntax.ml_unit]))
                                                 (FStar_Extraction_ML_Syntax.with_ty
                                                    t2)
                                           | uu____7509 ->
                                               failwith
                                                 "Impossible: Unexpected head term"
                                            in
                                         (head3, t2, rest))
                                  else err_uninst g head2 (vars, t1) top
                               in
                            (match uu____7312 with
                             | (head_ml1,head_t,args1) ->
                                 (match args1 with
                                  | [] ->
                                      let uu____7570 =
                                        maybe_eta_data_and_project_record g
                                          qual head_t head_ml1
                                         in
                                      (uu____7570,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        head_t)
                                  | uu____7571 ->
                                      extract_app_maybe_projector qual
                                        head_ml1
                                        (FStar_Extraction_ML_Syntax.E_PURE,
                                          head_t) args1)))
                   | FStar_Syntax_Syntax.Tm_fvar uu____7580 ->
                       let uu____7581 =
                         let uu____7594 =
                           FStar_Extraction_ML_UEnv.lookup_term g head2  in
                         match uu____7594 with
                         | (FStar_Util.Inr (uu____7613,x1,x2,x3),q) ->
                             ((x1, x2, x3), q)
                         | uu____7658 -> failwith "FIXME Ty"  in
                       (match uu____7581 with
                        | ((head_ml,(vars,t1),inst_ok),qual) ->
                            let has_typ_apps =
                              match args with
                              | (a,uu____7708)::uu____7709 -> is_type g a
                              | uu____7728 -> false  in
                            let uu____7737 =
                              match vars with
                              | uu____7766::uu____7767 when
                                  (Prims.op_Negation has_typ_apps) && inst_ok
                                  -> (head_ml, t1, args)
                              | uu____7778 ->
                                  let n1 = FStar_List.length vars  in
                                  if n1 <= (FStar_List.length args)
                                  then
                                    let uu____7806 =
                                      FStar_Util.first_N n1 args  in
                                    (match uu____7806 with
                                     | (prefix1,rest) ->
                                         let prefixAsMLTypes =
                                           FStar_List.map
                                             (fun uu____7895  ->
                                                match uu____7895 with
                                                | (x,uu____7901) ->
                                                    term_as_mlty g x) prefix1
                                            in
                                         let t2 =
                                           instantiate (vars, t1)
                                             prefixAsMLTypes
                                            in
                                         let mk_tapp e ty_args =
                                           match ty_args with
                                           | [] -> e
                                           | uu____7914 ->
                                               let uu___65_7917 = e  in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (FStar_Extraction_ML_Syntax.MLE_TApp
                                                      (e, ty_args));
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   =
                                                   (uu___65_7917.FStar_Extraction_ML_Syntax.mlty);
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___65_7917.FStar_Extraction_ML_Syntax.loc)
                                               }
                                            in
                                         let head3 =
                                           match head_ml.FStar_Extraction_ML_Syntax.expr
                                           with
                                           | FStar_Extraction_ML_Syntax.MLE_Name
                                               uu____7921 ->
                                               let uu___66_7922 =
                                                 mk_tapp head_ml
                                                   prefixAsMLTypes
                                                  in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (uu___66_7922.FStar_Extraction_ML_Syntax.expr);
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   = t2;
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___66_7922.FStar_Extraction_ML_Syntax.loc)
                                               }
                                           | FStar_Extraction_ML_Syntax.MLE_Var
                                               uu____7923 ->
                                               let uu___66_7924 =
                                                 mk_tapp head_ml
                                                   prefixAsMLTypes
                                                  in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (uu___66_7924.FStar_Extraction_ML_Syntax.expr);
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   = t2;
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___66_7924.FStar_Extraction_ML_Syntax.loc)
                                               }
                                           | FStar_Extraction_ML_Syntax.MLE_App
                                               (head3,{
                                                        FStar_Extraction_ML_Syntax.expr
                                                          =
                                                          FStar_Extraction_ML_Syntax.MLE_Const
                                                          (FStar_Extraction_ML_Syntax.MLC_Unit
                                                          );
                                                        FStar_Extraction_ML_Syntax.mlty
                                                          = uu____7926;
                                                        FStar_Extraction_ML_Syntax.loc
                                                          = uu____7927;_}::[])
                                               ->
                                               FStar_All.pipe_right
                                                 (FStar_Extraction_ML_Syntax.MLE_App
                                                    ((let uu___67_7933 =
                                                        mk_tapp head3
                                                          prefixAsMLTypes
                                                         in
                                                      {
                                                        FStar_Extraction_ML_Syntax.expr
                                                          =
                                                          (uu___67_7933.FStar_Extraction_ML_Syntax.expr);
                                                        FStar_Extraction_ML_Syntax.mlty
                                                          =
                                                          (FStar_Extraction_ML_Syntax.MLTY_Fun
                                                             (FStar_Extraction_ML_Syntax.ml_unit_ty,
                                                               FStar_Extraction_ML_Syntax.E_PURE,
                                                               t2));
                                                        FStar_Extraction_ML_Syntax.loc
                                                          =
                                                          (uu___67_7933.FStar_Extraction_ML_Syntax.loc)
                                                      }),
                                                      [FStar_Extraction_ML_Syntax.ml_unit]))
                                                 (FStar_Extraction_ML_Syntax.with_ty
                                                    t2)
                                           | uu____7934 ->
                                               failwith
                                                 "Impossible: Unexpected head term"
                                            in
                                         (head3, t2, rest))
                                  else err_uninst g head2 (vars, t1) top
                               in
                            (match uu____7737 with
                             | (head_ml1,head_t,args1) ->
                                 (match args1 with
                                  | [] ->
                                      let uu____7995 =
                                        maybe_eta_data_and_project_record g
                                          qual head_t head_ml1
                                         in
                                      (uu____7995,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        head_t)
                                  | uu____7996 ->
                                      extract_app_maybe_projector qual
                                        head_ml1
                                        (FStar_Extraction_ML_Syntax.E_PURE,
                                          head_t) args1)))
                   | uu____8005 ->
                       let uu____8006 = term_as_mlexpr g head2  in
                       (match uu____8006 with
                        | (head3,f,t1) ->
                            extract_app_maybe_projector
                              FStar_Pervasives_Native.None head3 (f, t1) args)))
       | FStar_Syntax_Syntax.Tm_ascribed (e0,(tc,uu____8024),f) ->
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
           let uu____8091 = check_term_as_mlexpr g e0 f1 t1  in
           (match uu____8091 with | (e,t2) -> (e, f1, t2))
       | FStar_Syntax_Syntax.Tm_let ((is_rec,lbs),e') ->
           let top_level = FStar_Syntax_Syntax.is_top_level lbs  in
           let uu____8122 =
             if is_rec
             then FStar_Syntax_Subst.open_let_rec lbs e'
             else
               (let uu____8136 = FStar_Syntax_Syntax.is_top_level lbs  in
                if uu____8136
                then (lbs, e')
                else
                  (let lb = FStar_List.hd lbs  in
                   let x =
                     let uu____8150 =
                       FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                     FStar_Syntax_Syntax.freshen_bv uu____8150  in
                   let lb1 =
                     let uu___68_8152 = lb  in
                     {
                       FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                       FStar_Syntax_Syntax.lbunivs =
                         (uu___68_8152.FStar_Syntax_Syntax.lbunivs);
                       FStar_Syntax_Syntax.lbtyp =
                         (uu___68_8152.FStar_Syntax_Syntax.lbtyp);
                       FStar_Syntax_Syntax.lbeff =
                         (uu___68_8152.FStar_Syntax_Syntax.lbeff);
                       FStar_Syntax_Syntax.lbdef =
                         (uu___68_8152.FStar_Syntax_Syntax.lbdef)
                     }  in
                   let e'1 =
                     FStar_Syntax_Subst.subst
                       [FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x)] e'
                      in
                   ([lb1], e'1)))
              in
           (match uu____8122 with
            | (lbs1,e'1) ->
                let lbs2 =
                  if top_level
                  then
                    FStar_All.pipe_right lbs1
                      (FStar_List.map
                         (fun lb  ->
                            let tcenv =
                              let uu____8184 =
                                FStar_Ident.lid_of_path
                                  (FStar_List.append
                                     (FStar_Pervasives_Native.fst
                                        g.FStar_Extraction_ML_UEnv.currentModule)
                                     [FStar_Pervasives_Native.snd
                                        g.FStar_Extraction_ML_UEnv.currentModule])
                                  FStar_Range.dummyRange
                                 in
                              FStar_TypeChecker_Env.set_current_module
                                g.FStar_Extraction_ML_UEnv.tcenv uu____8184
                               in
                            FStar_Extraction_ML_UEnv.debug g
                              (fun uu____8191  ->
                                 FStar_Options.set_option "debug_level"
                                   (FStar_Options.List
                                      [FStar_Options.String "Norm";
                                      FStar_Options.String "Extraction"]));
                            (let lbdef =
                               let uu____8195 = FStar_Options.ml_ish ()  in
                               if uu____8195
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
                             let uu___69_8199 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___69_8199.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___69_8199.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___69_8199.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___69_8199.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef
                             })))
                  else lbs1  in
                let maybe_generalize uu____8222 =
                  match uu____8222 with
                  | { FStar_Syntax_Syntax.lbname = lbname_;
                      FStar_Syntax_Syntax.lbunivs = uu____8242;
                      FStar_Syntax_Syntax.lbtyp = t1;
                      FStar_Syntax_Syntax.lbeff = lbeff;
                      FStar_Syntax_Syntax.lbdef = e;_} ->
                      let f_e = effect_as_etag g lbeff  in
                      let t2 = FStar_Syntax_Subst.compress t1  in
                      (match t2.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                           let uu____8312 = FStar_List.hd bs  in
                           FStar_All.pipe_right uu____8312 (is_type_binder g)
                           ->
                           let uu____8325 = FStar_Syntax_Subst.open_comp bs c
                              in
                           (match uu____8325 with
                            | (bs1,c1) ->
                                let uu____8350 =
                                  let uu____8357 =
                                    FStar_Util.prefix_until
                                      (fun x  ->
                                         let uu____8393 = is_type_binder g x
                                            in
                                         Prims.op_Negation uu____8393) bs1
                                     in
                                  match uu____8357 with
                                  | FStar_Pervasives_Native.None  ->
                                      (bs1,
                                        (FStar_Syntax_Util.comp_result c1))
                                  | FStar_Pervasives_Native.Some (bs2,b,rest)
                                      ->
                                      let uu____8481 =
                                        FStar_Syntax_Util.arrow (b :: rest)
                                          c1
                                         in
                                      (bs2, uu____8481)
                                   in
                                (match uu____8350 with
                                 | (tbinders,tbody) ->
                                     let n_tbinders =
                                       FStar_List.length tbinders  in
                                     let e1 =
                                       let uu____8526 = normalize_abs e  in
                                       FStar_All.pipe_right uu____8526
                                         FStar_Syntax_Util.unmeta
                                        in
                                     (match e1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Tm_abs
                                          (bs2,body,copt) ->
                                          let uu____8568 =
                                            FStar_Syntax_Subst.open_term bs2
                                              body
                                             in
                                          (match uu____8568 with
                                           | (bs3,body1) ->
                                               if
                                                 n_tbinders <=
                                                   (FStar_List.length bs3)
                                               then
                                                 let uu____8621 =
                                                   FStar_Util.first_N
                                                     n_tbinders bs3
                                                    in
                                                 (match uu____8621 with
                                                  | (targs,rest_args) ->
                                                      let expected_source_ty
                                                        =
                                                        let s =
                                                          FStar_List.map2
                                                            (fun uu____8709 
                                                               ->
                                                               fun uu____8710
                                                                  ->
                                                                 match 
                                                                   (uu____8709,
                                                                    uu____8710)
                                                                 with
                                                                 | ((x,uu____8728),
                                                                    (y,uu____8730))
                                                                    ->
                                                                    let uu____8739
                                                                    =
                                                                    let uu____8746
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    y  in
                                                                    (x,
                                                                    uu____8746)
                                                                     in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____8739)
                                                            tbinders targs
                                                           in
                                                        FStar_Syntax_Subst.subst
                                                          s tbody
                                                         in
                                                      let env =
                                                        FStar_List.fold_left
                                                          (fun env  ->
                                                             fun uu____8757 
                                                               ->
                                                               match uu____8757
                                                               with
                                                               | (a,uu____8763)
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
                                                        let uu____8772 =
                                                          FStar_All.pipe_right
                                                            targs
                                                            (FStar_List.map
                                                               (fun
                                                                  uu____8790 
                                                                  ->
                                                                  match uu____8790
                                                                  with
                                                                  | (x,uu____8796)
                                                                    ->
                                                                    FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                                    x))
                                                           in
                                                        (uu____8772,
                                                          expected_t)
                                                         in
                                                      let add_unit =
                                                        match rest_args with
                                                        | [] ->
                                                            let uu____8804 =
                                                              is_fstar_value
                                                                body1
                                                               in
                                                            Prims.op_Negation
                                                              uu____8804
                                                        | uu____8805 -> false
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
                                          uu____8874 ->
                                          let env =
                                            FStar_List.fold_left
                                              (fun env  ->
                                                 fun uu____8891  ->
                                                   match uu____8891 with
                                                   | (a,uu____8897) ->
                                                       FStar_Extraction_ML_UEnv.extend_ty
                                                         env a
                                                         FStar_Pervasives_Native.None)
                                              g tbinders
                                             in
                                          let expected_t =
                                            term_as_mlty env tbody  in
                                          let polytype =
                                            let uu____8906 =
                                              FStar_All.pipe_right tbinders
                                                (FStar_List.map
                                                   (fun uu____8918  ->
                                                      match uu____8918 with
                                                      | (x,uu____8924) ->
                                                          FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                            x))
                                               in
                                            (uu____8906, expected_t)  in
                                          let args =
                                            FStar_All.pipe_right tbinders
                                              (FStar_List.map
                                                 (fun uu____8940  ->
                                                    match uu____8940 with
                                                    | (bv,uu____8946) ->
                                                        let uu____8947 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            bv
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____8947
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
                                          uu____8989 ->
                                          let env =
                                            FStar_List.fold_left
                                              (fun env  ->
                                                 fun uu____9000  ->
                                                   match uu____9000 with
                                                   | (a,uu____9006) ->
                                                       FStar_Extraction_ML_UEnv.extend_ty
                                                         env a
                                                         FStar_Pervasives_Native.None)
                                              g tbinders
                                             in
                                          let expected_t =
                                            term_as_mlty env tbody  in
                                          let polytype =
                                            let uu____9015 =
                                              FStar_All.pipe_right tbinders
                                                (FStar_List.map
                                                   (fun uu____9027  ->
                                                      match uu____9027 with
                                                      | (x,uu____9033) ->
                                                          FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                            x))
                                               in
                                            (uu____9015, expected_t)  in
                                          let args =
                                            FStar_All.pipe_right tbinders
                                              (FStar_List.map
                                                 (fun uu____9049  ->
                                                    match uu____9049 with
                                                    | (bv,uu____9055) ->
                                                        let uu____9056 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            bv
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____9056
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
                                          uu____9098 ->
                                          let env =
                                            FStar_List.fold_left
                                              (fun env  ->
                                                 fun uu____9109  ->
                                                   match uu____9109 with
                                                   | (a,uu____9115) ->
                                                       FStar_Extraction_ML_UEnv.extend_ty
                                                         env a
                                                         FStar_Pervasives_Native.None)
                                              g tbinders
                                             in
                                          let expected_t =
                                            term_as_mlty env tbody  in
                                          let polytype =
                                            let uu____9124 =
                                              FStar_All.pipe_right tbinders
                                                (FStar_List.map
                                                   (fun uu____9136  ->
                                                      match uu____9136 with
                                                      | (x,uu____9142) ->
                                                          FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                            x))
                                               in
                                            (uu____9124, expected_t)  in
                                          let args =
                                            FStar_All.pipe_right tbinders
                                              (FStar_List.map
                                                 (fun uu____9158  ->
                                                    match uu____9158 with
                                                    | (bv,uu____9164) ->
                                                        let uu____9165 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            bv
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____9165
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
                                      | uu____9207 ->
                                          err_value_restriction e1)))
                       | uu____9226 ->
                           let expected_t = term_as_mlty g t2  in
                           (lbname_, f_e, (t2, ([], ([], expected_t))),
                             false, e))
                   in
                let check_lb env uu____9330 =
                  match uu____9330 with
                  | (nm,(lbname,f,(t1,(targs,polytype)),add_unit,e)) ->
                      let env1 =
                        FStar_List.fold_left
                          (fun env1  ->
                             fun uu____9465  ->
                               match uu____9465 with
                               | (a,uu____9471) ->
                                   FStar_Extraction_ML_UEnv.extend_ty env1 a
                                     FStar_Pervasives_Native.None) env targs
                         in
                      let expected_t = FStar_Pervasives_Native.snd polytype
                         in
                      let uu____9473 =
                        check_term_as_mlexpr env1 e f expected_t  in
                      (match uu____9473 with
                       | (e1,uu____9483) ->
                           let f1 = maybe_downgrade_eff env1 f expected_t  in
                           (f1,
                             {
                               FStar_Extraction_ML_Syntax.mllb_name = nm;
                               FStar_Extraction_ML_Syntax.mllb_tysc =
                                 (FStar_Pervasives_Native.Some polytype);
                               FStar_Extraction_ML_Syntax.mllb_add_unit =
                                 add_unit;
                               FStar_Extraction_ML_Syntax.mllb_def = e1;
                               FStar_Extraction_ML_Syntax.mllb_meta = [];
                               FStar_Extraction_ML_Syntax.print_typ = true
                             }))
                   in
                let lbs3 =
                  FStar_All.pipe_right lbs2 (FStar_List.map maybe_generalize)
                   in
                let uu____9550 =
                  FStar_List.fold_right
                    (fun lb  ->
                       fun uu____9641  ->
                         match uu____9641 with
                         | (env,lbs4) ->
                             let uu____9766 = lb  in
                             (match uu____9766 with
                              | (lbname,uu____9814,(t1,(uu____9816,polytype)),add_unit,uu____9819)
                                  ->
                                  let uu____9832 =
                                    FStar_Extraction_ML_UEnv.extend_lb env
                                      lbname t1 polytype add_unit true
                                     in
                                  (match uu____9832 with
                                   | (env1,nm) -> (env1, ((nm, lb) :: lbs4)))))
                    lbs3 (g, [])
                   in
                (match uu____9550 with
                 | (env_body,lbs4) ->
                     let env_def = if is_rec then env_body else g  in
                     let lbs5 =
                       FStar_All.pipe_right lbs4
                         (FStar_List.map (check_lb env_def))
                        in
                     let e'_rng = e'1.FStar_Syntax_Syntax.pos  in
                     let uu____10109 = term_as_mlexpr env_body e'1  in
                     (match uu____10109 with
                      | (e'2,f',t') ->
                          let f =
                            let uu____10126 =
                              let uu____10129 =
                                FStar_List.map FStar_Pervasives_Native.fst
                                  lbs5
                                 in
                              f' :: uu____10129  in
                            FStar_Extraction_ML_Util.join_l e'_rng
                              uu____10126
                             in
                          let is_rec1 =
                            if is_rec = true
                            then FStar_Extraction_ML_Syntax.Rec
                            else FStar_Extraction_ML_Syntax.NonRec  in
                          let uu____10138 =
                            let uu____10139 =
                              let uu____10140 =
                                let uu____10141 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    lbs5
                                   in
                                (is_rec1, uu____10141)  in
                              mk_MLE_Let top_level uu____10140 e'2  in
                            let uu____10150 =
                              FStar_Extraction_ML_Util.mlloc_of_range
                                t.FStar_Syntax_Syntax.pos
                               in
                            FStar_Extraction_ML_Syntax.with_ty_loc t'
                              uu____10139 uu____10150
                             in
                          (uu____10138, f, t'))))
       | FStar_Syntax_Syntax.Tm_match (scrutinee,pats) ->
           let uu____10189 = term_as_mlexpr g scrutinee  in
           (match uu____10189 with
            | (e,f_e,t_e) ->
                let uu____10205 = check_pats_for_ite pats  in
                (match uu____10205 with
                 | (b,then_e,else_e) ->
                     let no_lift x t1 = x  in
                     if b
                     then
                       (match (then_e, else_e) with
                        | (FStar_Pervasives_Native.Some
                           then_e1,FStar_Pervasives_Native.Some else_e1) ->
                            let uu____10262 = term_as_mlexpr g then_e1  in
                            (match uu____10262 with
                             | (then_mle,f_then,t_then) ->
                                 let uu____10278 = term_as_mlexpr g else_e1
                                    in
                                 (match uu____10278 with
                                  | (else_mle,f_else,t_else) ->
                                      let uu____10294 =
                                        let uu____10303 =
                                          type_leq g t_then t_else  in
                                        if uu____10303
                                        then (t_else, no_lift)
                                        else
                                          (let uu____10317 =
                                             type_leq g t_else t_then  in
                                           if uu____10317
                                           then (t_then, no_lift)
                                           else
                                             (FStar_Extraction_ML_Syntax.MLTY_Top,
                                               FStar_Extraction_ML_Syntax.apply_obj_repr))
                                         in
                                      (match uu____10294 with
                                       | (t_branch,maybe_lift1) ->
                                           let uu____10351 =
                                             let uu____10352 =
                                               let uu____10353 =
                                                 let uu____10362 =
                                                   maybe_lift1 then_mle
                                                     t_then
                                                    in
                                                 let uu____10363 =
                                                   let uu____10366 =
                                                     maybe_lift1 else_mle
                                                       t_else
                                                      in
                                                   FStar_Pervasives_Native.Some
                                                     uu____10366
                                                    in
                                                 (e, uu____10362,
                                                   uu____10363)
                                                  in
                                               FStar_Extraction_ML_Syntax.MLE_If
                                                 uu____10353
                                                in
                                             FStar_All.pipe_left
                                               (FStar_Extraction_ML_Syntax.with_ty
                                                  t_branch) uu____10352
                                              in
                                           let uu____10369 =
                                             FStar_Extraction_ML_Util.join
                                               then_e1.FStar_Syntax_Syntax.pos
                                               f_then f_else
                                              in
                                           (uu____10351, uu____10369,
                                             t_branch))))
                        | uu____10370 ->
                            failwith
                              "ITE pats matched but then and else expressions not found?")
                     else
                       (let uu____10386 =
                          FStar_All.pipe_right pats
                            (FStar_Util.fold_map
                               (fun compat  ->
                                  fun br  ->
                                    let uu____10495 =
                                      FStar_Syntax_Subst.open_branch br  in
                                    match uu____10495 with
                                    | (pat,when_opt,branch1) ->
                                        let uu____10539 =
                                          extract_pat g pat t_e
                                            term_as_mlexpr
                                           in
                                        (match uu____10539 with
                                         | (env,p,pat_t_compat) ->
                                             let uu____10597 =
                                               match when_opt with
                                               | FStar_Pervasives_Native.None
                                                    ->
                                                   (FStar_Pervasives_Native.None,
                                                     FStar_Extraction_ML_Syntax.E_PURE)
                                               | FStar_Pervasives_Native.Some
                                                   w ->
                                                   let uu____10619 =
                                                     term_as_mlexpr env w  in
                                                   (match uu____10619 with
                                                    | (w1,f_w,t_w) ->
                                                        let w2 =
                                                          maybe_coerce env w1
                                                            t_w
                                                            FStar_Extraction_ML_Syntax.ml_bool_ty
                                                           in
                                                        ((FStar_Pervasives_Native.Some
                                                            w2), f_w))
                                                in
                                             (match uu____10597 with
                                              | (when_opt1,f_when) ->
                                                  let uu____10668 =
                                                    term_as_mlexpr env
                                                      branch1
                                                     in
                                                  (match uu____10668 with
                                                   | (mlbranch,f_branch,t_branch)
                                                       ->
                                                       let uu____10702 =
                                                         FStar_All.pipe_right
                                                           p
                                                           (FStar_List.map
                                                              (fun
                                                                 uu____10779 
                                                                 ->
                                                                 match uu____10779
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
                                                         uu____10702)))))
                               true)
                           in
                        match uu____10386 with
                        | (pat_t_compat,mlbranches) ->
                            let mlbranches1 = FStar_List.flatten mlbranches
                               in
                            let e1 =
                              if pat_t_compat
                              then e
                              else
                                (FStar_Extraction_ML_UEnv.debug g
                                   (fun uu____10944  ->
                                      let uu____10945 =
                                        FStar_Extraction_ML_Code.string_of_mlexpr
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          e
                                         in
                                      let uu____10946 =
                                        FStar_Extraction_ML_Code.string_of_mlty
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          t_e
                                         in
                                      FStar_Util.print2
                                        "Coercing scrutinee %s from type %s because pattern type is incompatible\n"
                                        uu____10945 uu____10946);
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty t_e)
                                   (FStar_Extraction_ML_Syntax.MLE_Coerce
                                      (e, t_e,
                                        FStar_Extraction_ML_Syntax.MLTY_Top)))
                               in
                            (match mlbranches1 with
                             | [] ->
                                 let uu____10971 =
                                   let uu____10980 =
                                     let uu____10997 =
                                       FStar_Syntax_Syntax.lid_as_fv
                                         FStar_Parser_Const.failwith_lid
                                         FStar_Syntax_Syntax.Delta_constant
                                         FStar_Pervasives_Native.None
                                        in
                                     FStar_Extraction_ML_UEnv.lookup_fv g
                                       uu____10997
                                      in
                                   FStar_All.pipe_left FStar_Util.right
                                     uu____10980
                                    in
                                 (match uu____10971 with
                                  | (uu____11040,fw,uu____11042,uu____11043)
                                      ->
                                      let uu____11044 =
                                        let uu____11045 =
                                          let uu____11046 =
                                            let uu____11053 =
                                              let uu____11056 =
                                                FStar_All.pipe_left
                                                  (FStar_Extraction_ML_Syntax.with_ty
                                                     FStar_Extraction_ML_Syntax.ml_string_ty)
                                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                                     (FStar_Extraction_ML_Syntax.MLC_String
                                                        "unreachable"))
                                                 in
                                              [uu____11056]  in
                                            (fw, uu____11053)  in
                                          FStar_Extraction_ML_Syntax.MLE_App
                                            uu____11046
                                           in
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             FStar_Extraction_ML_Syntax.ml_unit_ty)
                                          uu____11045
                                         in
                                      (uu____11044,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        FStar_Extraction_ML_Syntax.ml_unit_ty))
                             | (uu____11059,uu____11060,(uu____11061,f_first,t_first))::rest
                                 ->
                                 let uu____11121 =
                                   FStar_List.fold_left
                                     (fun uu____11163  ->
                                        fun uu____11164  ->
                                          match (uu____11163, uu____11164)
                                          with
                                          | ((topt,f),(uu____11221,uu____11222,
                                                       (uu____11223,f_branch,t_branch)))
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
                                                    let uu____11279 =
                                                      type_leq g t1 t_branch
                                                       in
                                                    if uu____11279
                                                    then
                                                      FStar_Pervasives_Native.Some
                                                        t_branch
                                                    else
                                                      (let uu____11283 =
                                                         type_leq g t_branch
                                                           t1
                                                          in
                                                       if uu____11283
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
                                 (match uu____11121 with
                                  | (topt,f_match) ->
                                      let mlbranches2 =
                                        FStar_All.pipe_right mlbranches1
                                          (FStar_List.map
                                             (fun uu____11378  ->
                                                match uu____11378 with
                                                | (p,(wopt,uu____11407),
                                                   (b1,uu____11409,t1)) ->
                                                    let b2 =
                                                      match topt with
                                                      | FStar_Pervasives_Native.None
                                                           ->
                                                          FStar_Extraction_ML_Syntax.apply_obj_repr
                                                            b1 t1
                                                      | FStar_Pervasives_Native.Some
                                                          uu____11428 -> b1
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
                                      let uu____11433 =
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             t_match)
                                          (FStar_Extraction_ML_Syntax.MLE_Match
                                             (e1, mlbranches2))
                                         in
                                      (uu____11433, f_match, t_match)))))))

let ind_discriminator_body :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlmodule1
  =
  fun env  ->
    fun discName  ->
      fun constrName  ->
        let uu____11453 =
          let uu____11458 =
            FStar_TypeChecker_Env.lookup_lid
              env.FStar_Extraction_ML_UEnv.tcenv discName
             in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____11458  in
        match uu____11453 with
        | (uu____11483,fstar_disc_type) ->
            let wildcards =
              let uu____11492 =
                let uu____11493 = FStar_Syntax_Subst.compress fstar_disc_type
                   in
                uu____11493.FStar_Syntax_Syntax.n  in
              match uu____11492 with
              | FStar_Syntax_Syntax.Tm_arrow (binders,uu____11503) ->
                  let uu____11520 =
                    FStar_All.pipe_right binders
                      (FStar_List.filter
                         (fun uu___62_11552  ->
                            match uu___62_11552 with
                            | (uu____11559,FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____11560)) ->
                                true
                            | uu____11563 -> false))
                     in
                  FStar_All.pipe_right uu____11520
                    (FStar_List.map
                       (fun uu____11596  ->
                          let uu____11603 = fresh "_"  in
                          (uu____11603, FStar_Extraction_ML_Syntax.MLTY_Top)))
              | uu____11604 -> failwith "Discriminator must be a function"
               in
            let mlid = fresh "_discr_"  in
            let targ = FStar_Extraction_ML_Syntax.MLTY_Top  in
            let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top  in
            let discrBody =
              let uu____11615 =
                let uu____11616 =
                  let uu____11627 =
                    let uu____11628 =
                      let uu____11629 =
                        let uu____11644 =
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty targ)
                            (FStar_Extraction_ML_Syntax.MLE_Name ([], mlid))
                           in
                        let uu____11647 =
                          let uu____11658 =
                            let uu____11667 =
                              let uu____11668 =
                                let uu____11675 =
                                  FStar_Extraction_ML_Syntax.mlpath_of_lident
                                    constrName
                                   in
                                (uu____11675,
                                  [FStar_Extraction_ML_Syntax.MLP_Wild])
                                 in
                              FStar_Extraction_ML_Syntax.MLP_CTor uu____11668
                               in
                            let uu____11678 =
                              FStar_All.pipe_left
                                (FStar_Extraction_ML_Syntax.with_ty
                                   FStar_Extraction_ML_Syntax.ml_bool_ty)
                                (FStar_Extraction_ML_Syntax.MLE_Const
                                   (FStar_Extraction_ML_Syntax.MLC_Bool true))
                               in
                            (uu____11667, FStar_Pervasives_Native.None,
                              uu____11678)
                             in
                          let uu____11681 =
                            let uu____11692 =
                              let uu____11701 =
                                FStar_All.pipe_left
                                  (FStar_Extraction_ML_Syntax.with_ty
                                     FStar_Extraction_ML_Syntax.ml_bool_ty)
                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                     (FStar_Extraction_ML_Syntax.MLC_Bool
                                        false))
                                 in
                              (FStar_Extraction_ML_Syntax.MLP_Wild,
                                FStar_Pervasives_Native.None, uu____11701)
                               in
                            [uu____11692]  in
                          uu____11658 :: uu____11681  in
                        (uu____11644, uu____11647)  in
                      FStar_Extraction_ML_Syntax.MLE_Match uu____11629  in
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.ml_bool_ty) uu____11628
                     in
                  ((FStar_List.append wildcards [(mlid, targ)]), uu____11627)
                   in
                FStar_Extraction_ML_Syntax.MLE_Fun uu____11616  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty disc_ty) uu____11615
               in
            let uu____11756 =
              let uu____11757 =
                let uu____11760 =
                  let uu____11761 =
                    FStar_Extraction_ML_UEnv.convIdent
                      discName.FStar_Ident.ident
                     in
                  {
                    FStar_Extraction_ML_Syntax.mllb_name = uu____11761;
                    FStar_Extraction_ML_Syntax.mllb_tysc =
                      FStar_Pervasives_Native.None;
                    FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                    FStar_Extraction_ML_Syntax.mllb_def = discrBody;
                    FStar_Extraction_ML_Syntax.mllb_meta = [];
                    FStar_Extraction_ML_Syntax.print_typ = false
                  }  in
                [uu____11760]  in
              (FStar_Extraction_ML_Syntax.NonRec, uu____11757)  in
            FStar_Extraction_ML_Syntax.MLM_Let uu____11756
  