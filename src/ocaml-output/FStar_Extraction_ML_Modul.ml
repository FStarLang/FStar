open Prims
let (fail_exp :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun lid  ->
    fun t  ->
      let uu____13 =
        let uu____20 =
          let uu____21 =
            let uu____38 =
              FStar_Syntax_Syntax.fvar FStar_Parser_Const.failwith_lid
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            let uu____41 =
              let uu____52 = FStar_Syntax_Syntax.iarg t  in
              let uu____61 =
                let uu____72 =
                  let uu____81 =
                    let uu____82 =
                      let uu____89 =
                        let uu____90 =
                          let uu____91 =
                            let uu____96 =
                              let uu____97 =
                                FStar_Syntax_Print.lid_to_string lid  in
                              Prims.strcat "Not yet implemented:" uu____97
                               in
                            (uu____96, FStar_Range.dummyRange)  in
                          FStar_Const.Const_string uu____91  in
                        FStar_Syntax_Syntax.Tm_constant uu____90  in
                      FStar_Syntax_Syntax.mk uu____89  in
                    uu____82 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____81  in
                [uu____72]  in
              uu____52 :: uu____61  in
            (uu____38, uu____41)  in
          FStar_Syntax_Syntax.Tm_app uu____21  in
        FStar_Syntax_Syntax.mk uu____20  in
      uu____13 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (mangle_projector_lid : FStar_Ident.lident -> FStar_Ident.lident) =
  fun x  -> x 
let (lident_as_mlsymbol :
  FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlsymbol) =
  fun id1  ->
    FStar_Extraction_ML_Syntax.avoid_keyword
      (id1.FStar_Ident.ident).FStar_Ident.idText
  
let as_pair :
  'Auu____162 .
    'Auu____162 Prims.list ->
      ('Auu____162,'Auu____162) FStar_Pervasives_Native.tuple2
  =
  fun uu___391_173  ->
    match uu___391_173 with
    | a::b::[] -> (a, b)
    | uu____178 -> failwith "Expected a list with 2 elements"
  
let (flag_of_qual :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option)
  =
  fun uu___392_191  ->
    match uu___392_191 with
    | FStar_Syntax_Syntax.Assumption  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Assumed
    | FStar_Syntax_Syntax.Private  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Private
    | FStar_Syntax_Syntax.NoExtract  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.NoExtract
    | uu____194 -> FStar_Pervasives_Native.None
  
let rec (extract_meta :
  FStar_Syntax_Syntax.term ->
    FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option)
  =
  fun x  ->
    let uu____202 = FStar_Syntax_Subst.compress x  in
    match uu____202 with
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
        FStar_Syntax_Syntax.pos = uu____206;
        FStar_Syntax_Syntax.vars = uu____207;_} ->
        let uu____210 =
          let uu____211 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____211  in
        (match uu____210 with
         | "FStar.Pervasives.PpxDerivingShow" ->
             FStar_Pervasives_Native.Some
               FStar_Extraction_ML_Syntax.PpxDerivingShow
         | "FStar.Pervasives.PpxDerivingYoJson" ->
             FStar_Pervasives_Native.Some
               FStar_Extraction_ML_Syntax.PpxDerivingYoJson
         | "FStar.Pervasives.CInline" ->
             FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CInline
         | "FStar.Pervasives.Substitute" ->
             FStar_Pervasives_Native.Some
               FStar_Extraction_ML_Syntax.Substitute
         | "FStar.Pervasives.Gc" ->
             FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.GCType
         | "FStar.Pervasives.CAbstractStruct" ->
             FStar_Pervasives_Native.Some
               FStar_Extraction_ML_Syntax.CAbstract
         | uu____214 -> FStar_Pervasives_Native.None)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____216;
             FStar_Syntax_Syntax.vars = uu____217;_},({
                                                        FStar_Syntax_Syntax.n
                                                          =
                                                          FStar_Syntax_Syntax.Tm_constant
                                                          (FStar_Const.Const_string
                                                          (s,uu____219));
                                                        FStar_Syntax_Syntax.pos
                                                          = uu____220;
                                                        FStar_Syntax_Syntax.vars
                                                          = uu____221;_},uu____222)::[]);
        FStar_Syntax_Syntax.pos = uu____223;
        FStar_Syntax_Syntax.vars = uu____224;_} ->
        let uu____265 =
          let uu____266 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____266  in
        (match uu____265 with
         | "FStar.Pervasives.PpxDerivingShowConstant" ->
             FStar_Pervasives_Native.Some
               (FStar_Extraction_ML_Syntax.PpxDerivingShowConstant s)
         | "FStar.Pervasives.Comment" ->
             FStar_Pervasives_Native.Some
               (FStar_Extraction_ML_Syntax.Comment s)
         | "FStar.Pervasives.CPrologue" ->
             FStar_Pervasives_Native.Some
               (FStar_Extraction_ML_Syntax.CPrologue s)
         | "FStar.Pervasives.CEpilogue" ->
             FStar_Pervasives_Native.Some
               (FStar_Extraction_ML_Syntax.CEpilogue s)
         | "FStar.Pervasives.CConst" ->
             FStar_Pervasives_Native.Some
               (FStar_Extraction_ML_Syntax.CConst s)
         | "FStar.Pervasives.CCConv" ->
             FStar_Pervasives_Native.Some
               (FStar_Extraction_ML_Syntax.CCConv s)
         | uu____269 -> FStar_Pervasives_Native.None)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("KremlinPrivate",uu____270));
        FStar_Syntax_Syntax.pos = uu____271;
        FStar_Syntax_Syntax.vars = uu____272;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Private
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("c_inline",uu____275));
        FStar_Syntax_Syntax.pos = uu____276;
        FStar_Syntax_Syntax.vars = uu____277;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CInline
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("substitute",uu____280));
        FStar_Syntax_Syntax.pos = uu____281;
        FStar_Syntax_Syntax.vars = uu____282;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Substitute
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_meta (x1,uu____286);
        FStar_Syntax_Syntax.pos = uu____287;
        FStar_Syntax_Syntax.vars = uu____288;_} -> extract_meta x1
    | uu____295 -> FStar_Pervasives_Native.None
  
let (extract_metadata :
  FStar_Syntax_Syntax.term Prims.list ->
    FStar_Extraction_ML_Syntax.meta Prims.list)
  = fun metas  -> FStar_List.choose extract_meta metas 
let binders_as_mlty_binders :
  'Auu____313 .
    FStar_Extraction_ML_UEnv.env ->
      (FStar_Syntax_Syntax.bv,'Auu____313) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Extraction_ML_UEnv.env,Prims.string Prims.list)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bs  ->
      FStar_Util.fold_map
        (fun env1  ->
           fun uu____353  ->
             match uu____353 with
             | (bv,uu____363) ->
                 let uu____364 =
                   let uu____365 =
                     let uu____368 =
                       let uu____369 =
                         FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv  in
                       FStar_Extraction_ML_Syntax.MLTY_Var uu____369  in
                     FStar_Pervasives_Native.Some uu____368  in
                   FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____365  in
                 let uu____370 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv
                    in
                 (uu____364, uu____370)) env bs
  
let (extract_typ_abbrev :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.term Prims.list ->
          FStar_Syntax_Syntax.term ->
            (FStar_Extraction_ML_UEnv.env,FStar_Extraction_ML_Syntax.mlmodule1
                                            Prims.list)
              FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun fv  ->
      fun quals  ->
        fun attrs  ->
          fun def  ->
            let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            let def1 =
              let uu____414 =
                let uu____415 = FStar_Syntax_Subst.compress def  in
                FStar_All.pipe_right uu____415 FStar_Syntax_Util.unmeta  in
              FStar_All.pipe_right uu____414 FStar_Syntax_Util.un_uinst  in
            let def2 =
              match def1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_abs uu____423 ->
                  FStar_Extraction_ML_Term.normalize_abs def1
              | uu____442 -> def1  in
            let uu____443 =
              match def2.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____454) ->
                  FStar_Syntax_Subst.open_term bs body
              | uu____479 -> ([], def2)  in
            match uu____443 with
            | (bs,body) ->
                let assumed =
                  FStar_Util.for_some
                    (fun uu___393_496  ->
                       match uu___393_496 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____497 -> false) quals
                   in
                let uu____498 = binders_as_mlty_binders env bs  in
                (match uu____498 with
                 | (env1,ml_bs) ->
                     let body1 =
                       let uu____520 =
                         FStar_Extraction_ML_Term.term_as_mlty env1 body  in
                       FStar_All.pipe_right uu____520
                         (FStar_Extraction_ML_Util.eraseTypeDeep
                            (FStar_Extraction_ML_Util.udelta_unfold env1))
                        in
                     let mangled_projector =
                       let uu____524 =
                         FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___394_529  ->
                                 match uu___394_529 with
                                 | FStar_Syntax_Syntax.Projector uu____530 ->
                                     true
                                 | uu____535 -> false))
                          in
                       if uu____524
                       then
                         let mname = mangle_projector_lid lid  in
                         FStar_Pervasives_Native.Some
                           ((mname.FStar_Ident.ident).FStar_Ident.idText)
                       else FStar_Pervasives_Native.None  in
                     let metadata =
                       let uu____543 = extract_metadata attrs  in
                       let uu____546 = FStar_List.choose flag_of_qual quals
                          in
                       FStar_List.append uu____543 uu____546  in
                     let td =
                       let uu____552 =
                         let uu____553 = lident_as_mlsymbol lid  in
                         (assumed, uu____553, mangled_projector, ml_bs,
                           metadata,
                           (FStar_Pervasives_Native.Some
                              (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1)))
                          in
                       [uu____552]  in
                     let def3 =
                       let uu____561 =
                         let uu____562 =
                           let uu____563 = FStar_Ident.range_of_lid lid  in
                           FStar_Extraction_ML_Util.mlloc_of_range uu____563
                            in
                         FStar_Extraction_ML_Syntax.MLM_Loc uu____562  in
                       [uu____561; FStar_Extraction_ML_Syntax.MLM_Ty td]  in
                     let env2 =
                       let uu____565 =
                         FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___395_569  ->
                                 match uu___395_569 with
                                 | FStar_Syntax_Syntax.Assumption  -> true
                                 | FStar_Syntax_Syntax.New  -> true
                                 | uu____570 -> false))
                          in
                       if uu____565
                       then FStar_Extraction_ML_UEnv.extend_type_name env1 fv
                       else FStar_Extraction_ML_UEnv.extend_tydef env1 fv td
                        in
                     (env2, def3))
  
type data_constructor =
  {
  dname: FStar_Ident.lident ;
  dtyp: FStar_Syntax_Syntax.typ }
let (__proj__Mkdata_constructor__item__dname :
  data_constructor -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with
    | { dname = __fname__dname; dtyp = __fname__dtyp;_} -> __fname__dname
  
let (__proj__Mkdata_constructor__item__dtyp :
  data_constructor -> FStar_Syntax_Syntax.typ) =
  fun projectee  ->
    match projectee with
    | { dname = __fname__dname; dtyp = __fname__dtyp;_} -> __fname__dtyp
  
type inductive_family =
  {
  iname: FStar_Ident.lident ;
  iparams: FStar_Syntax_Syntax.binders ;
  ityp: FStar_Syntax_Syntax.term ;
  idatas: data_constructor Prims.list ;
  iquals: FStar_Syntax_Syntax.qualifier Prims.list ;
  imetadata: FStar_Extraction_ML_Syntax.metadata }
let (__proj__Mkinductive_family__item__iname :
  inductive_family -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; imetadata = __fname__imetadata;_} ->
        __fname__iname
  
let (__proj__Mkinductive_family__item__iparams :
  inductive_family -> FStar_Syntax_Syntax.binders) =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; imetadata = __fname__imetadata;_} ->
        __fname__iparams
  
let (__proj__Mkinductive_family__item__ityp :
  inductive_family -> FStar_Syntax_Syntax.term) =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; imetadata = __fname__imetadata;_} ->
        __fname__ityp
  
let (__proj__Mkinductive_family__item__idatas :
  inductive_family -> data_constructor Prims.list) =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; imetadata = __fname__imetadata;_} ->
        __fname__idatas
  
let (__proj__Mkinductive_family__item__iquals :
  inductive_family -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; imetadata = __fname__imetadata;_} ->
        __fname__iquals
  
let (__proj__Mkinductive_family__item__imetadata :
  inductive_family -> FStar_Extraction_ML_Syntax.metadata) =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; imetadata = __fname__imetadata;_} ->
        __fname__imetadata
  
let (print_ifamily : inductive_family -> unit) =
  fun i  ->
    let uu____735 = FStar_Syntax_Print.lid_to_string i.iname  in
    let uu____736 = FStar_Syntax_Print.binders_to_string " " i.iparams  in
    let uu____737 = FStar_Syntax_Print.term_to_string i.ityp  in
    let uu____738 =
      let uu____739 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let uu____750 = FStar_Syntax_Print.lid_to_string d.dname  in
                let uu____751 =
                  let uu____752 = FStar_Syntax_Print.term_to_string d.dtyp
                     in
                  Prims.strcat " : " uu____752  in
                Prims.strcat uu____750 uu____751))
         in
      FStar_All.pipe_right uu____739 (FStar_String.concat "\n\t\t")  in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____735 uu____736 uu____737
      uu____738
  
let (bundle_as_inductive_families :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.attribute Prims.list ->
          (FStar_Extraction_ML_UEnv.env,inductive_family Prims.list)
            FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun attrs  ->
          let uu____799 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun se  ->
                   match se.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,_us,bs,t,_mut_i,datas) ->
                       let uu____846 = FStar_Syntax_Subst.open_term bs t  in
                       (match uu____846 with
                        | (bs1,t1) ->
                            let datas1 =
                              FStar_All.pipe_right ses
                                (FStar_List.collect
                                   (fun se1  ->
                                      match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_datacon
                                          (d,uu____885,t2,l',nparams,uu____889)
                                          when FStar_Ident.lid_equals l l' ->
                                          let uu____894 =
                                            FStar_Syntax_Util.arrow_formals
                                              t2
                                             in
                                          (match uu____894 with
                                           | (bs',body) ->
                                               let uu____933 =
                                                 FStar_Util.first_N
                                                   (FStar_List.length bs1)
                                                   bs'
                                                  in
                                               (match uu____933 with
                                                | (bs_params,rest) ->
                                                    let subst1 =
                                                      FStar_List.map2
                                                        (fun uu____1024  ->
                                                           fun uu____1025  ->
                                                             match (uu____1024,
                                                                    uu____1025)
                                                             with
                                                             | ((b',uu____1051),
                                                                (b,uu____1053))
                                                                 ->
                                                                 let uu____1074
                                                                   =
                                                                   let uu____1081
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b  in
                                                                   (b',
                                                                    uu____1081)
                                                                    in
                                                                 FStar_Syntax_Syntax.NT
                                                                   uu____1074)
                                                        bs_params bs1
                                                       in
                                                    let t3 =
                                                      let uu____1087 =
                                                        let uu____1088 =
                                                          FStar_Syntax_Syntax.mk_Total
                                                            body
                                                           in
                                                        FStar_Syntax_Util.arrow
                                                          rest uu____1088
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____1087
                                                        (FStar_Syntax_Subst.subst
                                                           subst1)
                                                       in
                                                    [{ dname = d; dtyp = t3 }]))
                                      | uu____1091 -> []))
                               in
                            let metadata =
                              let uu____1095 =
                                extract_metadata
                                  (FStar_List.append
                                     se.FStar_Syntax_Syntax.sigattrs attrs)
                                 in
                              let uu____1098 =
                                FStar_List.choose flag_of_qual quals  in
                              FStar_List.append uu____1095 uu____1098  in
                            let env2 =
                              let uu____1102 =
                                FStar_Syntax_Syntax.lid_as_fv l
                                  FStar_Syntax_Syntax.delta_constant
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Extraction_ML_UEnv.extend_type_name env1
                                uu____1102
                               in
                            (env2,
                              [{
                                 iname = l;
                                 iparams = bs1;
                                 ityp = t1;
                                 idatas = datas1;
                                 iquals = (se.FStar_Syntax_Syntax.sigquals);
                                 imetadata = metadata
                               }]))
                   | uu____1105 -> (env1, [])) env ses
             in
          match uu____799 with
          | (env1,ifams) -> (env1, (FStar_List.flatten ifams))
  
type env_t = FStar_Extraction_ML_UEnv.env
let (extract_bundle :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t,FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun se  ->
      let extract_ctor ml_tyvars env1 ctor =
        let mlt =
          let uu____1191 =
            FStar_Extraction_ML_Term.term_as_mlty env1 ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env1) uu____1191
           in
        let steps =
          [FStar_TypeChecker_Env.Inlining;
          FStar_TypeChecker_Env.UnfoldUntil
            FStar_Syntax_Syntax.delta_constant;
          FStar_TypeChecker_Env.EraseUniverses;
          FStar_TypeChecker_Env.AllowUnboundUniverses]  in
        let names1 =
          let uu____1198 =
            let uu____1199 =
              let uu____1202 =
                FStar_TypeChecker_Normalize.normalize steps
                  env1.FStar_Extraction_ML_UEnv.tcenv ctor.dtyp
                 in
              FStar_Syntax_Subst.compress uu____1202  in
            uu____1199.FStar_Syntax_Syntax.n  in
          match uu____1198 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,uu____1206) ->
              FStar_List.map
                (fun uu____1238  ->
                   match uu____1238 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____1246;
                        FStar_Syntax_Syntax.sort = uu____1247;_},uu____1248)
                       -> ppname.FStar_Ident.idText) bs
          | uu____1255 -> []  in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____1262 =
          let uu____1263 =
            FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
          FStar_Pervasives_Native.fst uu____1263  in
        let uu____1268 =
          let uu____1279 = lident_as_mlsymbol ctor.dname  in
          let uu____1280 =
            let uu____1287 = FStar_Extraction_ML_Util.argTypes mlt  in
            FStar_List.zip names1 uu____1287  in
          (uu____1279, uu____1280)  in
        (uu____1262, uu____1268)  in
      let extract_one_family env1 ind =
        let uu____1339 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____1339 with
        | (env2,vars) ->
            let uu____1376 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor vars) env2)
               in
            (match uu____1376 with
             | (env3,ctors) ->
                 let uu____1469 = FStar_Syntax_Util.arrow_formals ind.ityp
                    in
                 (match uu____1469 with
                  | (indices,uu____1507) ->
                      let ml_params =
                        let uu____1531 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____1554  ->
                                    let uu____1561 =
                                      FStar_Util.string_of_int i  in
                                    Prims.strcat "'dummyV" uu____1561))
                           in
                        FStar_List.append vars uu____1531  in
                      let tbody =
                        let uu____1563 =
                          FStar_Util.find_opt
                            (fun uu___396_1568  ->
                               match uu___396_1568 with
                               | FStar_Syntax_Syntax.RecordType uu____1569 ->
                                   true
                               | uu____1578 -> false) ind.iquals
                           in
                        match uu____1563 with
                        | FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____1589 = FStar_List.hd ctors  in
                            (match uu____1589 with
                             | (uu____1610,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id1  ->
                                        fun uu____1647  ->
                                          match uu____1647 with
                                          | (uu____1656,ty) ->
                                              let lid =
                                                FStar_Ident.lid_of_ids
                                                  (FStar_List.append ns [id1])
                                                 in
                                              let uu____1659 =
                                                lident_as_mlsymbol lid  in
                                              (uu____1659, ty)) ids c_ty
                                    in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____1660 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors
                         in
                      let uu____1663 =
                        let uu____1682 = lident_as_mlsymbol ind.iname  in
                        (false, uu____1682, FStar_Pervasives_Native.None,
                          ml_params, (ind.imetadata),
                          (FStar_Pervasives_Native.Some tbody))
                         in
                      (env3, uu____1663)))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____1716,t,uu____1718,uu____1719,uu____1720);
            FStar_Syntax_Syntax.sigrng = uu____1721;
            FStar_Syntax_Syntax.sigquals = uu____1722;
            FStar_Syntax_Syntax.sigmeta = uu____1723;
            FStar_Syntax_Syntax.sigattrs = uu____1724;_}::[],uu____1725),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____1742 = extract_ctor [] env { dname = l; dtyp = t }  in
          (match uu____1742 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____1788),quals) ->
          let uu____1802 =
            bundle_as_inductive_families env ses quals
              se.FStar_Syntax_Syntax.sigattrs
             in
          (match uu____1802 with
           | (env1,ifams) ->
               let uu____1821 =
                 FStar_Util.fold_map extract_one_family env1 ifams  in
               (match uu____1821 with
                | (env2,td) -> (env2, [FStar_Extraction_ML_Syntax.MLM_Ty td])))
      | uu____1914 -> failwith "Unexpected signature element"
  
let (maybe_register_plugin :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
  =
  fun g  ->
    fun se  ->
      let w =
        FStar_Extraction_ML_Syntax.with_ty
          FStar_Extraction_ML_Syntax.MLTY_Top
         in
      let plugin_with_arity attrs =
        FStar_Util.find_map attrs
          (fun t  ->
             let uu____1968 = FStar_Syntax_Util.head_and_args t  in
             match uu____1968 with
             | (head1,args) ->
                 let uu____2015 =
                   let uu____2016 =
                     FStar_Syntax_Util.is_fvar FStar_Parser_Const.plugin_attr
                       head1
                      in
                   Prims.op_Negation uu____2016  in
                 if uu____2015
                 then FStar_Pervasives_Native.None
                 else
                   (match args with
                    | ({
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_int (s,uu____2029));
                         FStar_Syntax_Syntax.pos = uu____2030;
                         FStar_Syntax_Syntax.vars = uu____2031;_},uu____2032)::[]
                        ->
                        let uu____2069 =
                          let uu____2072 = FStar_Util.int_of_string s  in
                          FStar_Pervasives_Native.Some uu____2072  in
                        FStar_Pervasives_Native.Some uu____2069
                    | uu____2075 ->
                        FStar_Pervasives_Native.Some
                          FStar_Pervasives_Native.None))
         in
      let uu____2088 =
        let uu____2089 = FStar_Options.codegen ()  in
        uu____2089 <> (FStar_Pervasives_Native.Some FStar_Options.Plugin)  in
      if uu____2088
      then []
      else
        (let uu____2097 = plugin_with_arity se.FStar_Syntax_Syntax.sigattrs
            in
         match uu____2097 with
         | FStar_Pervasives_Native.None  -> []
         | FStar_Pervasives_Native.Some arity_opt ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
                  let mk_registration lb =
                    let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                       in
                    let fv_lid1 =
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                       in
                    let fv_t = lb.FStar_Syntax_Syntax.lbtyp  in
                    let ml_name_str =
                      let uu____2135 =
                        let uu____2136 = FStar_Ident.string_of_lid fv_lid1
                           in
                        FStar_Extraction_ML_Syntax.MLC_String uu____2136  in
                      FStar_Extraction_ML_Syntax.MLE_Const uu____2135  in
                    let uu____2137 =
                      FStar_Extraction_ML_Util.interpret_plugin_as_term_fun
                        g.FStar_Extraction_ML_UEnv.tcenv fv fv_t arity_opt
                        ml_name_str
                       in
                    match uu____2137 with
                    | FStar_Pervasives_Native.Some
                        (interp,nbe_interp,arity,plugin) ->
                        let uu____2162 =
                          if plugin
                          then
                            ("FStar_Tactics_Native.register_plugin",
                              [interp; nbe_interp])
                          else
                            ("FStar_Tactics_Native.register_tactic",
                              [interp])
                           in
                        (match uu____2162 with
                         | (register,args) ->
                             let h =
                               let uu____2189 =
                                 let uu____2190 =
                                   let uu____2191 =
                                     FStar_Ident.lid_of_str register  in
                                   FStar_Extraction_ML_Syntax.mlpath_of_lident
                                     uu____2191
                                    in
                                 FStar_Extraction_ML_Syntax.MLE_Name
                                   uu____2190
                                  in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    FStar_Extraction_ML_Syntax.MLTY_Top)
                                 uu____2189
                                in
                             let arity1 =
                               let uu____2193 =
                                 let uu____2194 =
                                   let uu____2205 =
                                     FStar_Util.string_of_int arity  in
                                   (uu____2205, FStar_Pervasives_Native.None)
                                    in
                                 FStar_Extraction_ML_Syntax.MLC_Int
                                   uu____2194
                                  in
                               FStar_Extraction_ML_Syntax.MLE_Const
                                 uu____2193
                                in
                             let app =
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    FStar_Extraction_ML_Syntax.MLTY_Top)
                                 (FStar_Extraction_ML_Syntax.MLE_App
                                    (h,
                                      (FStar_List.append
                                         [w ml_name_str; w arity1] args)))
                                in
                             [FStar_Extraction_ML_Syntax.MLM_Top app])
                    | FStar_Pervasives_Native.None  -> []  in
                  FStar_List.collect mk_registration
                    (FStar_Pervasives_Native.snd lbs)
              | uu____2229 -> []))
  
let rec (extract_sig :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t,FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun g  ->
    fun se  ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u  ->
           let uu____2256 = FStar_Syntax_Print.sigelt_to_string se  in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____2256);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____2263 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____2272 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____2289 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_TypeChecker_Env.is_reifiable_effect
             g.FStar_Extraction_ML_UEnv.tcenv ed.FStar_Syntax_Syntax.mname
           ->
           let extend_env g1 lid ml_name tm tysc =
             let uu____2335 =
               let uu____2340 =
                 FStar_Syntax_Syntax.lid_as_fv lid
                   FStar_Syntax_Syntax.delta_equational
                   FStar_Pervasives_Native.None
                  in
               FStar_Extraction_ML_UEnv.extend_fv' g1 uu____2340 ml_name tysc
                 false false
                in
             match uu____2335 with
             | (g2,mangled_name) ->
                 ((let uu____2348 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          g2.FStar_Extraction_ML_UEnv.tcenv)
                       (FStar_Options.Other "ExtractionReify")
                      in
                   if uu____2348
                   then FStar_Util.print1 "Mangled name: %s\n" mangled_name
                   else ());
                  (let lb =
                     {
                       FStar_Extraction_ML_Syntax.mllb_name = mangled_name;
                       FStar_Extraction_ML_Syntax.mllb_tysc =
                         FStar_Pervasives_Native.None;
                       FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                       FStar_Extraction_ML_Syntax.mllb_def = tm;
                       FStar_Extraction_ML_Syntax.mllb_meta = [];
                       FStar_Extraction_ML_Syntax.print_typ = false
                     }  in
                   (g2,
                     (FStar_Extraction_ML_Syntax.MLM_Let
                        (FStar_Extraction_ML_Syntax.NonRec, [lb])))))
              in
           let rec extract_fv tm =
             (let uu____2364 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify")
                 in
              if uu____2364
              then
                let uu____2365 = FStar_Syntax_Print.term_to_string tm  in
                FStar_Util.print1 "extract_fv term: %s\n" uu____2365
              else ());
             (let uu____2367 =
                let uu____2368 = FStar_Syntax_Subst.compress tm  in
                uu____2368.FStar_Syntax_Syntax.n  in
              match uu____2367 with
              | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____2376) ->
                  extract_fv tm1
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let mlp =
                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                     in
                  let uu____2383 =
                    let uu____2392 = FStar_Extraction_ML_UEnv.lookup_fv g fv
                       in
                    FStar_All.pipe_left FStar_Util.right uu____2392  in
                  (match uu____2383 with
                   | (uu____2449,uu____2450,tysc,uu____2452) ->
                       let uu____2453 =
                         FStar_All.pipe_left
                           (FStar_Extraction_ML_Syntax.with_ty
                              FStar_Extraction_ML_Syntax.MLTY_Top)
                           (FStar_Extraction_ML_Syntax.MLE_Name mlp)
                          in
                       (uu____2453, tysc))
              | uu____2454 -> failwith "Not an fv")
              in
           let extract_action g1 a =
             (let uu____2476 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g1.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify")
                 in
              if uu____2476
              then
                let uu____2477 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_typ
                   in
                let uu____2478 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_defn
                   in
                FStar_Util.print2 "Action type %s and term %s\n" uu____2477
                  uu____2478
              else ());
             (let uu____2480 = FStar_Extraction_ML_UEnv.action_name ed a  in
              match uu____2480 with
              | (a_nm,a_lid) ->
                  let lbname =
                    let uu____2496 =
                      FStar_Syntax_Syntax.new_bv
                        (FStar_Pervasives_Native.Some
                           ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                        FStar_Syntax_Syntax.tun
                       in
                    FStar_Util.Inl uu____2496  in
                  let lb =
                    FStar_Syntax_Syntax.mk_lb
                      (lbname, (a.FStar_Syntax_Syntax.action_univs),
                        FStar_Parser_Const.effect_Tot_lid,
                        (a.FStar_Syntax_Syntax.action_typ),
                        (a.FStar_Syntax_Syntax.action_defn),
                        ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                     in
                  let lbs = (false, [lb])  in
                  let action_lb =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_let
                         (lbs, FStar_Syntax_Util.exp_false_bool))
                      FStar_Pervasives_Native.None
                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                     in
                  let uu____2520 =
                    FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb  in
                  (match uu____2520 with
                   | (a_let,uu____2532,ty) ->
                       ((let uu____2535 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug
                                g1.FStar_Extraction_ML_UEnv.tcenv)
                             (FStar_Options.Other "ExtractionReify")
                            in
                         if uu____2535
                         then
                           let uu____2536 =
                             FStar_Extraction_ML_Code.string_of_mlexpr a_nm
                               a_let
                              in
                           FStar_Util.print1 "Extracted action term: %s\n"
                             uu____2536
                         else ());
                        (let uu____2538 =
                           match a_let.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_Let
                               ((uu____2555,mllb::[]),uu____2557) ->
                               (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                                with
                                | FStar_Pervasives_Native.Some tysc ->
                                    ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                      tysc)
                                | FStar_Pervasives_Native.None  ->
                                    failwith "No type scheme")
                           | uu____2587 -> failwith "Impossible"  in
                         match uu____2538 with
                         | (exp,tysc) ->
                             ((let uu____2611 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug
                                      g1.FStar_Extraction_ML_UEnv.tcenv)
                                   (FStar_Options.Other "ExtractionReify")
                                  in
                               if uu____2611
                               then
                                 ((let uu____2613 =
                                     FStar_Extraction_ML_Code.string_of_mlty
                                       a_nm
                                       (FStar_Pervasives_Native.snd tysc)
                                      in
                                   FStar_Util.print1
                                     "Extracted action type: %s\n" uu____2613);
                                  FStar_List.iter
                                    (fun x  ->
                                       FStar_Util.print1 "and binders: %s\n"
                                         x)
                                    (FStar_Pervasives_Native.fst tysc))
                               else ());
                              extend_env g1 a_lid a_nm exp tysc)))))
              in
           let uu____2619 =
             let uu____2624 =
               extract_fv
                 (FStar_Pervasives_Native.snd
                    ed.FStar_Syntax_Syntax.return_repr)
                in
             match uu____2624 with
             | (return_tm,ty_sc) ->
                 let uu____2639 =
                   FStar_Extraction_ML_UEnv.monad_op_name ed "return"  in
                 (match uu____2639 with
                  | (return_nm,return_lid) ->
                      extend_env g return_lid return_nm return_tm ty_sc)
              in
           (match uu____2619 with
            | (g1,return_decl) ->
                let uu____2658 =
                  let uu____2663 =
                    extract_fv
                      (FStar_Pervasives_Native.snd
                         ed.FStar_Syntax_Syntax.bind_repr)
                     in
                  match uu____2663 with
                  | (bind_tm,ty_sc) ->
                      let uu____2678 =
                        FStar_Extraction_ML_UEnv.monad_op_name ed "bind"  in
                      (match uu____2678 with
                       | (bind_nm,bind_lid) ->
                           extend_env g1 bind_lid bind_nm bind_tm ty_sc)
                   in
                (match uu____2658 with
                 | (g2,bind_decl) ->
                     let uu____2697 =
                       FStar_Util.fold_map extract_action g2
                         ed.FStar_Syntax_Syntax.actions
                        in
                     (match uu____2697 with
                      | (g3,actions) ->
                          (g3,
                            (FStar_List.append [return_decl; bind_decl]
                               actions)))))
       | FStar_Syntax_Syntax.Sig_splice uu____2718 ->
           failwith "impossible: trying to extract splice"
       | FStar_Syntax_Syntax.Sig_new_effect uu____2731 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____2735,t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let uu____2743 =
             let uu____2744 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___397_2748  ->
                       match uu___397_2748 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____2749 -> false))
                in
             Prims.op_Negation uu____2744  in
           if uu____2743
           then (g, [])
           else
             (let uu____2759 = FStar_Syntax_Util.arrow_formals t  in
              match uu____2759 with
              | (bs,uu____2781) ->
                  let fv =
                    FStar_Syntax_Syntax.lid_as_fv lid
                      FStar_Syntax_Syntax.delta_constant
                      FStar_Pervasives_Native.None
                     in
                  let uu____2803 =
                    FStar_Syntax_Util.abs bs FStar_Syntax_Syntax.t_unit
                      FStar_Pervasives_Native.None
                     in
                  extract_typ_abbrev g fv quals attrs uu____2803)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____2805) when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____2815 =
             let uu____2824 =
               FStar_TypeChecker_Env.open_universes_in
                 g.FStar_Extraction_ML_UEnv.tcenv
                 lb.FStar_Syntax_Syntax.lbunivs
                 [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp]
                in
             match uu____2824 with
             | (tcenv,uu____2842,def_typ) ->
                 let uu____2848 = as_pair def_typ  in (tcenv, uu____2848)
              in
           (match uu____2815 with
            | (tcenv,(lbdef,lbtyp)) ->
                let lbtyp1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.Beta;
                    FStar_TypeChecker_Env.UnfoldUntil
                      FStar_Syntax_Syntax.delta_constant] tcenv lbtyp
                   in
                let lbdef1 =
                  FStar_TypeChecker_Normalize.eta_expand_with_type tcenv
                    lbdef lbtyp1
                   in
                let uu____2872 =
                  FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                extract_typ_abbrev g uu____2872 quals
                  se.FStar_Syntax_Syntax.sigattrs lbdef1)
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____2874) ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____2885 =
             let uu____2892 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let
                    (lbs, FStar_Syntax_Util.exp_false_bool))
                 FStar_Pervasives_Native.None se.FStar_Syntax_Syntax.sigrng
                in
             FStar_Extraction_ML_Term.term_as_mlexpr g uu____2892  in
           (match uu____2885 with
            | (ml_let,uu____2908,uu____2909) ->
                (match ml_let.FStar_Extraction_ML_Syntax.expr with
                 | FStar_Extraction_ML_Syntax.MLE_Let
                     ((flavor,bindings),uu____2918) ->
                     let flags1 = FStar_List.choose flag_of_qual quals  in
                     let flags' = extract_metadata attrs  in
                     let uu____2935 =
                       FStar_List.fold_left2
                         (fun uu____2961  ->
                            fun ml_lb  ->
                              fun uu____2963  ->
                                match (uu____2961, uu____2963) with
                                | ((env,ml_lbs),{
                                                  FStar_Syntax_Syntax.lbname
                                                    = lbname;
                                                  FStar_Syntax_Syntax.lbunivs
                                                    = uu____2985;
                                                  FStar_Syntax_Syntax.lbtyp =
                                                    t;
                                                  FStar_Syntax_Syntax.lbeff =
                                                    uu____2987;
                                                  FStar_Syntax_Syntax.lbdef =
                                                    uu____2988;
                                                  FStar_Syntax_Syntax.lbattrs
                                                    = uu____2989;
                                                  FStar_Syntax_Syntax.lbpos =
                                                    uu____2990;_})
                                    ->
                                    let uu____3015 =
                                      FStar_All.pipe_right
                                        ml_lb.FStar_Extraction_ML_Syntax.mllb_meta
                                        (FStar_List.contains
                                           FStar_Extraction_ML_Syntax.Erased)
                                       in
                                    if uu____3015
                                    then (env, ml_lbs)
                                    else
                                      (let lb_lid =
                                         let uu____3028 =
                                           let uu____3031 =
                                             FStar_Util.right lbname  in
                                           uu____3031.FStar_Syntax_Syntax.fv_name
                                            in
                                         uu____3028.FStar_Syntax_Syntax.v  in
                                       let flags'' =
                                         let uu____3035 =
                                           let uu____3036 =
                                             FStar_Syntax_Subst.compress t
                                              in
                                           uu____3036.FStar_Syntax_Syntax.n
                                            in
                                         match uu____3035 with
                                         | FStar_Syntax_Syntax.Tm_arrow
                                             (uu____3041,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Comp
                                                             {
                                                               FStar_Syntax_Syntax.comp_univs
                                                                 = uu____3042;
                                                               FStar_Syntax_Syntax.effect_name
                                                                 = e;
                                                               FStar_Syntax_Syntax.result_typ
                                                                 = uu____3044;
                                                               FStar_Syntax_Syntax.effect_args
                                                                 = uu____3045;
                                                               FStar_Syntax_Syntax.flags
                                                                 = uu____3046;_};
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____3047;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____3048;_})
                                             when
                                             let uu____3083 =
                                               FStar_Ident.string_of_lid e
                                                in
                                             uu____3083 =
                                               "FStar.HyperStack.ST.StackInline"
                                             ->
                                             [FStar_Extraction_ML_Syntax.StackInline]
                                         | uu____3084 -> []  in
                                       let meta =
                                         FStar_List.append flags1
                                           (FStar_List.append flags' flags'')
                                          in
                                       let ml_lb1 =
                                         let uu___401_3089 = ml_lb  in
                                         {
                                           FStar_Extraction_ML_Syntax.mllb_name
                                             =
                                             (uu___401_3089.FStar_Extraction_ML_Syntax.mllb_name);
                                           FStar_Extraction_ML_Syntax.mllb_tysc
                                             =
                                             (uu___401_3089.FStar_Extraction_ML_Syntax.mllb_tysc);
                                           FStar_Extraction_ML_Syntax.mllb_add_unit
                                             =
                                             (uu___401_3089.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                           FStar_Extraction_ML_Syntax.mllb_def
                                             =
                                             (uu___401_3089.FStar_Extraction_ML_Syntax.mllb_def);
                                           FStar_Extraction_ML_Syntax.mllb_meta
                                             = meta;
                                           FStar_Extraction_ML_Syntax.print_typ
                                             =
                                             (uu___401_3089.FStar_Extraction_ML_Syntax.print_typ)
                                         }  in
                                       let uu____3090 =
                                         let uu____3095 =
                                           FStar_All.pipe_right quals
                                             (FStar_Util.for_some
                                                (fun uu___398_3100  ->
                                                   match uu___398_3100 with
                                                   | FStar_Syntax_Syntax.Projector
                                                       uu____3101 -> true
                                                   | uu____3106 -> false))
                                            in
                                         if uu____3095
                                         then
                                           let mname =
                                             let uu____3118 =
                                               mangle_projector_lid lb_lid
                                                in
                                             FStar_All.pipe_right uu____3118
                                               FStar_Extraction_ML_Syntax.mlpath_of_lident
                                              in
                                           let uu____3125 =
                                             let uu____3130 =
                                               FStar_Util.right lbname  in
                                             let uu____3131 =
                                               FStar_Util.must
                                                 ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                in
                                             FStar_Extraction_ML_UEnv.extend_fv'
                                               env uu____3130 mname
                                               uu____3131
                                               ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                               false
                                              in
                                           match uu____3125 with
                                           | (env1,uu____3137) ->
                                               (env1,
                                                 (let uu___402_3139 = ml_lb1
                                                     in
                                                  {
                                                    FStar_Extraction_ML_Syntax.mllb_name
                                                      =
                                                      (FStar_Pervasives_Native.snd
                                                         mname);
                                                    FStar_Extraction_ML_Syntax.mllb_tysc
                                                      =
                                                      (uu___402_3139.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                    FStar_Extraction_ML_Syntax.mllb_add_unit
                                                      =
                                                      (uu___402_3139.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                    FStar_Extraction_ML_Syntax.mllb_def
                                                      =
                                                      (uu___402_3139.FStar_Extraction_ML_Syntax.mllb_def);
                                                    FStar_Extraction_ML_Syntax.mllb_meta
                                                      =
                                                      (uu___402_3139.FStar_Extraction_ML_Syntax.mllb_meta);
                                                    FStar_Extraction_ML_Syntax.print_typ
                                                      =
                                                      (uu___402_3139.FStar_Extraction_ML_Syntax.print_typ)
                                                  }))
                                         else
                                           (let uu____3143 =
                                              let uu____3144 =
                                                let uu____3149 =
                                                  FStar_Util.must
                                                    ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                   in
                                                FStar_Extraction_ML_UEnv.extend_lb
                                                  env lbname t uu____3149
                                                  ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                                  false
                                                 in
                                              FStar_All.pipe_left
                                                FStar_Pervasives_Native.fst
                                                uu____3144
                                               in
                                            (uu____3143, ml_lb1))
                                          in
                                       match uu____3090 with
                                       | (g1,ml_lb2) ->
                                           (g1, (ml_lb2 :: ml_lbs)))) 
                         (g, []) bindings (FStar_Pervasives_Native.snd lbs)
                        in
                     (match uu____2935 with
                      | (g1,ml_lbs') ->
                          let uu____3180 =
                            let uu____3183 =
                              let uu____3186 =
                                let uu____3187 =
                                  FStar_Extraction_ML_Util.mlloc_of_range
                                    se.FStar_Syntax_Syntax.sigrng
                                   in
                                FStar_Extraction_ML_Syntax.MLM_Loc uu____3187
                                 in
                              [uu____3186;
                              FStar_Extraction_ML_Syntax.MLM_Let
                                (flavor, (FStar_List.rev ml_lbs'))]
                               in
                            let uu____3190 = maybe_register_plugin g1 se  in
                            FStar_List.append uu____3183 uu____3190  in
                          (g1, uu____3180))
                 | uu____3195 ->
                     let uu____3196 =
                       let uu____3197 =
                         FStar_Extraction_ML_Code.string_of_mlexpr
                           g.FStar_Extraction_ML_UEnv.currentModule ml_let
                          in
                       FStar_Util.format1
                         "Impossible: Translated a let to a non-let: %s"
                         uu____3197
                        in
                     failwith uu____3196))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____3205,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____3210 =
             (FStar_All.pipe_right quals
                (FStar_List.contains FStar_Syntax_Syntax.Assumption))
               &&
               (let uu____3214 =
                  FStar_TypeChecker_Util.must_erase_for_extraction
                    g.FStar_Extraction_ML_UEnv.tcenv t
                   in
                Prims.op_Negation uu____3214)
              in
           if uu____3210
           then
             let always_fail =
               let imp =
                 let uu____3225 = FStar_Syntax_Util.arrow_formals t  in
                 match uu____3225 with
                 | ([],t1) ->
                     let b =
                       let uu____3268 =
                         FStar_Syntax_Syntax.gen_bv "_"
                           FStar_Pervasives_Native.None t1
                          in
                       FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                         uu____3268
                        in
                     let uu____3275 = fail_exp lid t1  in
                     FStar_Syntax_Util.abs [b] uu____3275
                       FStar_Pervasives_Native.None
                 | (bs,t1) ->
                     let uu____3312 = fail_exp lid t1  in
                     FStar_Syntax_Util.abs bs uu____3312
                       FStar_Pervasives_Native.None
                  in
               let uu___403_3315 = se  in
               let uu____3316 =
                 let uu____3317 =
                   let uu____3324 =
                     let uu____3325 =
                       let uu____3328 =
                         let uu____3329 =
                           let uu____3334 =
                             FStar_Syntax_Syntax.lid_as_fv lid
                               FStar_Syntax_Syntax.delta_constant
                               FStar_Pervasives_Native.None
                              in
                           FStar_Util.Inr uu____3334  in
                         {
                           FStar_Syntax_Syntax.lbname = uu____3329;
                           FStar_Syntax_Syntax.lbunivs = [];
                           FStar_Syntax_Syntax.lbtyp = t;
                           FStar_Syntax_Syntax.lbeff =
                             FStar_Parser_Const.effect_ML_lid;
                           FStar_Syntax_Syntax.lbdef = imp;
                           FStar_Syntax_Syntax.lbattrs = [];
                           FStar_Syntax_Syntax.lbpos =
                             (imp.FStar_Syntax_Syntax.pos)
                         }  in
                       [uu____3328]  in
                     (false, uu____3325)  in
                   (uu____3324, [])  in
                 FStar_Syntax_Syntax.Sig_let uu____3317  in
               {
                 FStar_Syntax_Syntax.sigel = uu____3316;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___403_3315.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___403_3315.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___403_3315.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___403_3315.FStar_Syntax_Syntax.sigattrs)
               }  in
             let uu____3341 = extract_sig g always_fail  in
             (match uu____3341 with
              | (g1,mlm) ->
                  let uu____3360 =
                    FStar_Util.find_map quals
                      (fun uu___399_3365  ->
                         match uu___399_3365 with
                         | FStar_Syntax_Syntax.Discriminator l ->
                             FStar_Pervasives_Native.Some l
                         | uu____3369 -> FStar_Pervasives_Native.None)
                     in
                  (match uu____3360 with
                   | FStar_Pervasives_Native.Some l ->
                       let uu____3377 =
                         let uu____3380 =
                           let uu____3381 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng
                              in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____3381  in
                         let uu____3382 =
                           let uu____3385 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l
                              in
                           [uu____3385]  in
                         uu____3380 :: uu____3382  in
                       (g1, uu____3377)
                   | uu____3388 ->
                       let uu____3391 =
                         FStar_Util.find_map quals
                           (fun uu___400_3397  ->
                              match uu___400_3397 with
                              | FStar_Syntax_Syntax.Projector (l,uu____3401)
                                  -> FStar_Pervasives_Native.Some l
                              | uu____3402 -> FStar_Pervasives_Native.None)
                          in
                       (match uu____3391 with
                        | FStar_Pervasives_Native.Some uu____3409 -> (g1, [])
                        | uu____3412 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____3421 = FStar_Extraction_ML_Term.term_as_mlexpr g e  in
           (match uu____3421 with
            | (ml_main,uu____3435,uu____3436) ->
                let uu____3437 =
                  let uu____3440 =
                    let uu____3441 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng
                       in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____3441  in
                  [uu____3440; FStar_Extraction_ML_Syntax.MLM_Top ml_main]
                   in
                (g, uu____3437))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____3444 ->
           failwith "impossible -- removed by tc.fs"
       | FStar_Syntax_Syntax.Sig_assume uu____3451 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____3460 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____3463 -> (g, [])
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (FStar_Syntax_Util.process_pragma p se.FStar_Syntax_Syntax.sigrng;
            (g, [])))
  
let (extract_iface :
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.modul -> env_t) =
  fun g  ->
    fun m  ->
      let uu____3492 =
        FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____3492 FStar_Pervasives_Native.fst
  
let (extract' :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Extraction_ML_UEnv.env,FStar_Extraction_ML_Syntax.mllib
                                      Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun g  ->
    fun m  ->
      FStar_Syntax_Syntax.reset_gensym ();
      (let uu____3538 = FStar_Options.restore_cmd_line_options true  in
       let name =
         FStar_Extraction_ML_Syntax.mlpath_of_lident
           m.FStar_Syntax_Syntax.name
          in
       let g1 =
         let uu___404_3541 = g  in
         let uu____3542 =
           FStar_TypeChecker_Env.set_current_module
             g.FStar_Extraction_ML_UEnv.tcenv m.FStar_Syntax_Syntax.name
            in
         {
           FStar_Extraction_ML_UEnv.tcenv = uu____3542;
           FStar_Extraction_ML_UEnv.gamma =
             (uu___404_3541.FStar_Extraction_ML_UEnv.gamma);
           FStar_Extraction_ML_UEnv.tydefs =
             (uu___404_3541.FStar_Extraction_ML_UEnv.tydefs);
           FStar_Extraction_ML_UEnv.type_names =
             (uu___404_3541.FStar_Extraction_ML_UEnv.type_names);
           FStar_Extraction_ML_UEnv.currentModule = name
         }  in
       let uu____3543 =
         FStar_Util.fold_map extract_sig g1
           m.FStar_Syntax_Syntax.declarations
          in
       match uu____3543 with
       | (g2,sigs) ->
           let mlm = FStar_List.flatten sigs  in
           let is_kremlin =
             let uu____3572 = FStar_Options.codegen ()  in
             uu____3572 =
               (FStar_Pervasives_Native.Some FStar_Options.Kremlin)
              in
           let uu____3577 =
             (((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
                (is_kremlin ||
                   (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)))
               &&
               (FStar_Options.should_extract
                  (m.FStar_Syntax_Syntax.name).FStar_Ident.str)
              in
           if uu____3577
           then
             ((let uu____3585 =
                 FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name
                  in
               FStar_Util.print1 "Extracted module %s\n" uu____3585);
              (g2,
                [FStar_Extraction_ML_Syntax.MLLib
                   [(name, (FStar_Pervasives_Native.Some ([], mlm)),
                      (FStar_Extraction_ML_Syntax.MLLib []))]]))
           else (g2, []))
  
let (extract :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Extraction_ML_UEnv.env,FStar_Extraction_ML_Syntax.mllib
                                      Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun g  ->
    fun m  ->
      let uu____3653 = FStar_Options.debug_any ()  in
      if uu____3653
      then
        let msg =
          let uu____3661 =
            FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name  in
          FStar_Util.format1 "Extracting module %s\n" uu____3661  in
        FStar_Util.measure_execution_time msg
          (fun uu____3669  -> extract' g m)
      else extract' g m
  