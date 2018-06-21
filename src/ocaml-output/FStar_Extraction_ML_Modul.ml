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
            let uu____36 =
              FStar_Syntax_Syntax.fvar FStar_Parser_Const.failwith_lid
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            let uu____39 =
              let uu____48 = FStar_Syntax_Syntax.iarg t  in
              let uu____55 =
                let uu____64 =
                  let uu____71 =
                    let uu____72 =
                      let uu____79 =
                        let uu____80 =
                          let uu____81 =
                            let uu____86 =
                              let uu____87 =
                                FStar_Syntax_Print.lid_to_string lid  in
                              Prims.strcat "Not yet implemented:" uu____87
                               in
                            (uu____86, FStar_Range.dummyRange)  in
                          FStar_Const.Const_string uu____81  in
                        FStar_Syntax_Syntax.Tm_constant uu____80  in
                      FStar_Syntax_Syntax.mk uu____79  in
                    uu____72 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____71  in
                [uu____64]  in
              uu____48 :: uu____55  in
            (uu____36, uu____39)  in
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
  'Auu____142 .
    'Auu____142 Prims.list ->
      ('Auu____142,'Auu____142) FStar_Pervasives_Native.tuple2
  =
  fun uu___378_153  ->
    match uu___378_153 with
    | a::b::[] -> (a, b)
    | uu____158 -> failwith "Expected a list with 2 elements"
  
let (flag_of_qual :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option)
  =
  fun uu___379_171  ->
    match uu___379_171 with
    | FStar_Syntax_Syntax.Assumption  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Assumed
    | FStar_Syntax_Syntax.Private  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Private
    | FStar_Syntax_Syntax.NoExtract  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.NoExtract
    | uu____174 -> FStar_Pervasives_Native.None
  
let rec (extract_meta :
  FStar_Syntax_Syntax.term ->
    FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option)
  =
  fun x  ->
    let uu____182 = FStar_Syntax_Subst.compress x  in
    match uu____182 with
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
        FStar_Syntax_Syntax.pos = uu____186;
        FStar_Syntax_Syntax.vars = uu____187;_} ->
        let uu____190 =
          let uu____191 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____191  in
        (match uu____190 with
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
         | uu____194 -> FStar_Pervasives_Native.None)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____196;
             FStar_Syntax_Syntax.vars = uu____197;_},({
                                                        FStar_Syntax_Syntax.n
                                                          =
                                                          FStar_Syntax_Syntax.Tm_constant
                                                          (FStar_Const.Const_string
                                                          (s,uu____199));
                                                        FStar_Syntax_Syntax.pos
                                                          = uu____200;
                                                        FStar_Syntax_Syntax.vars
                                                          = uu____201;_},uu____202)::[]);
        FStar_Syntax_Syntax.pos = uu____203;
        FStar_Syntax_Syntax.vars = uu____204;_} ->
        let uu____235 =
          let uu____236 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____236  in
        (match uu____235 with
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
         | uu____239 -> FStar_Pervasives_Native.None)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("KremlinPrivate",uu____240));
        FStar_Syntax_Syntax.pos = uu____241;
        FStar_Syntax_Syntax.vars = uu____242;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Private
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("c_inline",uu____245));
        FStar_Syntax_Syntax.pos = uu____246;
        FStar_Syntax_Syntax.vars = uu____247;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CInline
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("substitute",uu____250));
        FStar_Syntax_Syntax.pos = uu____251;
        FStar_Syntax_Syntax.vars = uu____252;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Substitute
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_meta (x1,uu____256);
        FStar_Syntax_Syntax.pos = uu____257;
        FStar_Syntax_Syntax.vars = uu____258;_} -> extract_meta x1
    | uu____265 -> FStar_Pervasives_Native.None
  
let (extract_metadata :
  FStar_Syntax_Syntax.term Prims.list ->
    FStar_Extraction_ML_Syntax.meta Prims.list)
  = fun metas  -> FStar_List.choose extract_meta metas 
let binders_as_mlty_binders :
  'Auu____283 .
    FStar_Extraction_ML_UEnv.env ->
      (FStar_Syntax_Syntax.bv,'Auu____283) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Extraction_ML_UEnv.env,Prims.string Prims.list)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bs  ->
      FStar_Util.fold_map
        (fun env1  ->
           fun uu____323  ->
             match uu____323 with
             | (bv,uu____333) ->
                 let uu____334 =
                   let uu____335 =
                     let uu____338 =
                       let uu____339 =
                         FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv  in
                       FStar_Extraction_ML_Syntax.MLTY_Var uu____339  in
                     FStar_Pervasives_Native.Some uu____338  in
                   FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____335  in
                 let uu____340 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv
                    in
                 (uu____334, uu____340)) env bs
  
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
              let uu____384 =
                let uu____385 = FStar_Syntax_Subst.compress def  in
                FStar_All.pipe_right uu____385 FStar_Syntax_Util.unmeta  in
              FStar_All.pipe_right uu____384 FStar_Syntax_Util.un_uinst  in
            let def2 =
              match def1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_abs uu____393 ->
                  FStar_Extraction_ML_Term.normalize_abs def1
              | uu____410 -> def1  in
            let uu____411 =
              match def2.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____422) ->
                  FStar_Syntax_Subst.open_term bs body
              | uu____443 -> ([], def2)  in
            match uu____411 with
            | (bs,body) ->
                let assumed =
                  FStar_Util.for_some
                    (fun uu___380_458  ->
                       match uu___380_458 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____459 -> false) quals
                   in
                let uu____460 = binders_as_mlty_binders env bs  in
                (match uu____460 with
                 | (env1,ml_bs) ->
                     let body1 =
                       let uu____480 =
                         FStar_Extraction_ML_Term.term_as_mlty env1 body  in
                       FStar_All.pipe_right uu____480
                         (FStar_Extraction_ML_Util.eraseTypeDeep
                            (FStar_Extraction_ML_Util.udelta_unfold env1))
                        in
                     let mangled_projector =
                       let uu____484 =
                         FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___381_489  ->
                                 match uu___381_489 with
                                 | FStar_Syntax_Syntax.Projector uu____490 ->
                                     true
                                 | uu____495 -> false))
                          in
                       if uu____484
                       then
                         let mname = mangle_projector_lid lid  in
                         FStar_Pervasives_Native.Some
                           ((mname.FStar_Ident.ident).FStar_Ident.idText)
                       else FStar_Pervasives_Native.None  in
                     let metadata =
                       let uu____503 = extract_metadata attrs  in
                       let uu____506 = FStar_List.choose flag_of_qual quals
                          in
                       FStar_List.append uu____503 uu____506  in
                     let td =
                       let uu____512 =
                         let uu____513 = lident_as_mlsymbol lid  in
                         (assumed, uu____513, mangled_projector, ml_bs,
                           metadata,
                           (FStar_Pervasives_Native.Some
                              (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1)))
                          in
                       [uu____512]  in
                     let def3 =
                       let uu____521 =
                         let uu____522 =
                           let uu____523 = FStar_Ident.range_of_lid lid  in
                           FStar_Extraction_ML_Util.mlloc_of_range uu____523
                            in
                         FStar_Extraction_ML_Syntax.MLM_Loc uu____522  in
                       [uu____521; FStar_Extraction_ML_Syntax.MLM_Ty td]  in
                     let env2 =
                       let uu____525 =
                         FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___382_529  ->
                                 match uu___382_529 with
                                 | FStar_Syntax_Syntax.Assumption  -> true
                                 | FStar_Syntax_Syntax.New  -> true
                                 | uu____530 -> false))
                          in
                       if uu____525
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
    let uu____695 = FStar_Syntax_Print.lid_to_string i.iname  in
    let uu____696 = FStar_Syntax_Print.binders_to_string " " i.iparams  in
    let uu____697 = FStar_Syntax_Print.term_to_string i.ityp  in
    let uu____698 =
      let uu____699 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let uu____710 = FStar_Syntax_Print.lid_to_string d.dname  in
                let uu____711 =
                  let uu____712 = FStar_Syntax_Print.term_to_string d.dtyp
                     in
                  Prims.strcat " : " uu____712  in
                Prims.strcat uu____710 uu____711))
         in
      FStar_All.pipe_right uu____699 (FStar_String.concat "\n\t\t")  in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____695 uu____696 uu____697
      uu____698
  
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
          let uu____759 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun se  ->
                   match se.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,_us,bs,t,_mut_i,datas) ->
                       let uu____806 = FStar_Syntax_Subst.open_term bs t  in
                       (match uu____806 with
                        | (bs1,t1) ->
                            let datas1 =
                              FStar_All.pipe_right ses
                                (FStar_List.collect
                                   (fun se1  ->
                                      match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_datacon
                                          (d,uu____845,t2,l',nparams,uu____849)
                                          when FStar_Ident.lid_equals l l' ->
                                          let uu____854 =
                                            FStar_Syntax_Util.arrow_formals
                                              t2
                                             in
                                          (match uu____854 with
                                           | (bs',body) ->
                                               let uu____887 =
                                                 FStar_Util.first_N
                                                   (FStar_List.length bs1)
                                                   bs'
                                                  in
                                               (match uu____887 with
                                                | (bs_params,rest) ->
                                                    let subst1 =
                                                      FStar_List.map2
                                                        (fun uu____958  ->
                                                           fun uu____959  ->
                                                             match (uu____958,
                                                                    uu____959)
                                                             with
                                                             | ((b',uu____977),
                                                                (b,uu____979))
                                                                 ->
                                                                 let uu____988
                                                                   =
                                                                   let uu____995
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b  in
                                                                   (b',
                                                                    uu____995)
                                                                    in
                                                                 FStar_Syntax_Syntax.NT
                                                                   uu____988)
                                                        bs_params bs1
                                                       in
                                                    let t3 =
                                                      let uu____1001 =
                                                        let uu____1002 =
                                                          FStar_Syntax_Syntax.mk_Total
                                                            body
                                                           in
                                                        FStar_Syntax_Util.arrow
                                                          rest uu____1002
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____1001
                                                        (FStar_Syntax_Subst.subst
                                                           subst1)
                                                       in
                                                    [{ dname = d; dtyp = t3 }]))
                                      | uu____1005 -> []))
                               in
                            let metadata =
                              let uu____1009 =
                                extract_metadata
                                  (FStar_List.append
                                     se.FStar_Syntax_Syntax.sigattrs attrs)
                                 in
                              let uu____1012 =
                                FStar_List.choose flag_of_qual quals  in
                              FStar_List.append uu____1009 uu____1012  in
                            let env2 =
                              let uu____1016 =
                                FStar_Syntax_Syntax.lid_as_fv l
                                  FStar_Syntax_Syntax.delta_constant
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Extraction_ML_UEnv.extend_type_name env1
                                uu____1016
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
                   | uu____1019 -> (env1, [])) env ses
             in
          match uu____759 with
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
          let uu____1105 =
            FStar_Extraction_ML_Term.term_as_mlty env1 ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env1) uu____1105
           in
        let steps =
          [FStar_TypeChecker_Normalize.Inlining;
          FStar_TypeChecker_Normalize.UnfoldUntil
            FStar_Syntax_Syntax.delta_constant;
          FStar_TypeChecker_Normalize.EraseUniverses;
          FStar_TypeChecker_Normalize.AllowUnboundUniverses]  in
        let names1 =
          let uu____1112 =
            let uu____1113 =
              let uu____1116 =
                FStar_TypeChecker_Normalize.normalize steps
                  env1.FStar_Extraction_ML_UEnv.tcenv ctor.dtyp
                 in
              FStar_Syntax_Subst.compress uu____1116  in
            uu____1113.FStar_Syntax_Syntax.n  in
          match uu____1112 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,uu____1120) ->
              FStar_List.map
                (fun uu____1146  ->
                   match uu____1146 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____1152;
                        FStar_Syntax_Syntax.sort = uu____1153;_},uu____1154)
                       -> ppname.FStar_Ident.idText) bs
          | uu____1157 -> []  in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____1164 =
          let uu____1165 =
            FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
          FStar_Pervasives_Native.fst uu____1165  in
        let uu____1170 =
          let uu____1181 = lident_as_mlsymbol ctor.dname  in
          let uu____1182 =
            let uu____1189 = FStar_Extraction_ML_Util.argTypes mlt  in
            FStar_List.zip names1 uu____1189  in
          (uu____1181, uu____1182)  in
        (uu____1164, uu____1170)  in
      let extract_one_family env1 ind =
        let uu____1241 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____1241 with
        | (env2,vars) ->
            let uu____1276 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor vars) env2)
               in
            (match uu____1276 with
             | (env3,ctors) ->
                 let uu____1369 = FStar_Syntax_Util.arrow_formals ind.ityp
                    in
                 (match uu____1369 with
                  | (indices,uu____1405) ->
                      let ml_params =
                        let uu____1425 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____1444  ->
                                    let uu____1449 =
                                      FStar_Util.string_of_int i  in
                                    Prims.strcat "'dummyV" uu____1449))
                           in
                        FStar_List.append vars uu____1425  in
                      let tbody =
                        let uu____1451 =
                          FStar_Util.find_opt
                            (fun uu___383_1456  ->
                               match uu___383_1456 with
                               | FStar_Syntax_Syntax.RecordType uu____1457 ->
                                   true
                               | uu____1466 -> false) ind.iquals
                           in
                        match uu____1451 with
                        | FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____1477 = FStar_List.hd ctors  in
                            (match uu____1477 with
                             | (uu____1498,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id1  ->
                                        fun uu____1535  ->
                                          match uu____1535 with
                                          | (uu____1544,ty) ->
                                              let lid =
                                                FStar_Ident.lid_of_ids
                                                  (FStar_List.append ns [id1])
                                                 in
                                              let uu____1547 =
                                                lident_as_mlsymbol lid  in
                                              (uu____1547, ty)) ids c_ty
                                    in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____1548 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors
                         in
                      let uu____1551 =
                        let uu____1570 = lident_as_mlsymbol ind.iname  in
                        (false, uu____1570, FStar_Pervasives_Native.None,
                          ml_params, (ind.imetadata),
                          (FStar_Pervasives_Native.Some tbody))
                         in
                      (env3, uu____1551)))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____1604,t,uu____1606,uu____1607,uu____1608);
            FStar_Syntax_Syntax.sigrng = uu____1609;
            FStar_Syntax_Syntax.sigquals = uu____1610;
            FStar_Syntax_Syntax.sigmeta = uu____1611;
            FStar_Syntax_Syntax.sigattrs = uu____1612;_}::[],uu____1613),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____1630 = extract_ctor [] env { dname = l; dtyp = t }  in
          (match uu____1630 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____1676),quals) ->
          let uu____1690 =
            bundle_as_inductive_families env ses quals
              se.FStar_Syntax_Syntax.sigattrs
             in
          (match uu____1690 with
           | (env1,ifams) ->
               let uu____1709 =
                 FStar_Util.fold_map extract_one_family env1 ifams  in
               (match uu____1709 with
                | (env2,td) -> (env2, [FStar_Extraction_ML_Syntax.MLM_Ty td])))
      | uu____1802 -> failwith "Unexpected signature element"
  
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
      let uu____1834 =
        (let uu____1837 = FStar_Options.codegen ()  in
         uu____1837 <> (FStar_Pervasives_Native.Some FStar_Options.Plugin))
          ||
          (let uu____1843 =
             FStar_Syntax_Util.has_attribute se.FStar_Syntax_Syntax.sigattrs
               FStar_Parser_Const.plugin_attr
              in
           Prims.op_Negation uu____1843)
         in
      if uu____1834
      then []
      else
        (match se.FStar_Syntax_Syntax.sigel with
         | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
             let mk_registration lb =
               let fv =
                 let uu____1866 =
                   let uu____1869 =
                     FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                   uu____1869.FStar_Syntax_Syntax.fv_name  in
                 uu____1866.FStar_Syntax_Syntax.v  in
               let fv_t = lb.FStar_Syntax_Syntax.lbtyp  in
               let ml_name_str =
                 let uu____1874 =
                   let uu____1875 = FStar_Ident.string_of_lid fv  in
                   FStar_Extraction_ML_Syntax.MLC_String uu____1875  in
                 FStar_Extraction_ML_Syntax.MLE_Const uu____1874  in
               let uu____1876 =
                 FStar_Extraction_ML_Util.interpret_plugin_as_term_fun
                   g.FStar_Extraction_ML_UEnv.tcenv fv fv_t ml_name_str
                  in
               match uu____1876 with
               | FStar_Pervasives_Native.Some (interp,arity,plugin) ->
                   let register =
                     if plugin
                     then "FStar_Tactics_Native.register_plugin"
                     else "FStar_Tactics_Native.register_tactic"  in
                   let h =
                     let uu____1899 =
                       let uu____1900 =
                         let uu____1901 = FStar_Ident.lid_of_str register  in
                         FStar_Extraction_ML_Syntax.mlpath_of_lident
                           uu____1901
                          in
                       FStar_Extraction_ML_Syntax.MLE_Name uu____1900  in
                     FStar_All.pipe_left
                       (FStar_Extraction_ML_Syntax.with_ty
                          FStar_Extraction_ML_Syntax.MLTY_Top) uu____1899
                      in
                   let arity1 =
                     let uu____1903 =
                       let uu____1904 =
                         let uu____1915 = FStar_Util.string_of_int arity  in
                         (uu____1915, FStar_Pervasives_Native.None)  in
                       FStar_Extraction_ML_Syntax.MLC_Int uu____1904  in
                     FStar_Extraction_ML_Syntax.MLE_Const uu____1903  in
                   let app =
                     FStar_All.pipe_left
                       (FStar_Extraction_ML_Syntax.with_ty
                          FStar_Extraction_ML_Syntax.MLTY_Top)
                       (FStar_Extraction_ML_Syntax.MLE_App
                          (h, [w ml_name_str; w arity1; interp]))
                      in
                   [FStar_Extraction_ML_Syntax.MLM_Top app]
               | FStar_Pervasives_Native.None  -> []  in
             FStar_List.collect mk_registration
               (FStar_Pervasives_Native.snd lbs)
         | uu____1937 -> [])
  
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
           let uu____1964 = FStar_Syntax_Print.sigelt_to_string se  in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____1964);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____1971 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____1980 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____1997 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
           ->
           let extend_env g1 lid ml_name tm tysc =
             let uu____2045 =
               let uu____2050 =
                 FStar_Syntax_Syntax.lid_as_fv lid
                   FStar_Syntax_Syntax.delta_equational
                   FStar_Pervasives_Native.None
                  in
               FStar_Extraction_ML_UEnv.extend_fv' g1 uu____2050 ml_name tysc
                 false false
                in
             match uu____2045 with
             | (g2,mangled_name) ->
                 ((let uu____2058 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          g2.FStar_Extraction_ML_UEnv.tcenv)
                       (FStar_Options.Other "ExtractionReify")
                      in
                   if uu____2058
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
             (let uu____2074 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify")
                 in
              if uu____2074
              then
                let uu____2075 = FStar_Syntax_Print.term_to_string tm  in
                FStar_Util.print1 "extract_fv term: %s\n" uu____2075
              else ());
             (let uu____2077 =
                let uu____2078 = FStar_Syntax_Subst.compress tm  in
                uu____2078.FStar_Syntax_Syntax.n  in
              match uu____2077 with
              | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____2086) ->
                  extract_fv tm1
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let mlp =
                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                     in
                  let uu____2093 =
                    let uu____2102 = FStar_Extraction_ML_UEnv.lookup_fv g fv
                       in
                    FStar_All.pipe_left FStar_Util.right uu____2102  in
                  (match uu____2093 with
                   | (uu____2159,uu____2160,tysc,uu____2162) ->
                       let uu____2163 =
                         FStar_All.pipe_left
                           (FStar_Extraction_ML_Syntax.with_ty
                              FStar_Extraction_ML_Syntax.MLTY_Top)
                           (FStar_Extraction_ML_Syntax.MLE_Name mlp)
                          in
                       (uu____2163, tysc))
              | uu____2164 -> failwith "Not an fv")
              in
           let extract_action g1 a =
             (let uu____2186 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g1.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify")
                 in
              if uu____2186
              then
                let uu____2187 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_typ
                   in
                let uu____2188 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_defn
                   in
                FStar_Util.print2 "Action type %s and term %s\n" uu____2187
                  uu____2188
              else ());
             (let uu____2190 = FStar_Extraction_ML_UEnv.action_name ed a  in
              match uu____2190 with
              | (a_nm,a_lid) ->
                  let lbname =
                    let uu____2206 =
                      FStar_Syntax_Syntax.new_bv
                        (FStar_Pervasives_Native.Some
                           ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                        FStar_Syntax_Syntax.tun
                       in
                    FStar_Util.Inl uu____2206  in
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
                  let uu____2230 =
                    FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb  in
                  (match uu____2230 with
                   | (a_let,uu____2242,ty) ->
                       ((let uu____2245 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug
                                g1.FStar_Extraction_ML_UEnv.tcenv)
                             (FStar_Options.Other "ExtractionReify")
                            in
                         if uu____2245
                         then
                           let uu____2246 =
                             FStar_Extraction_ML_Code.string_of_mlexpr a_nm
                               a_let
                              in
                           FStar_Util.print1 "Extracted action term: %s\n"
                             uu____2246
                         else ());
                        (let uu____2248 =
                           match a_let.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_Let
                               ((uu____2265,mllb::[]),uu____2267) ->
                               (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                                with
                                | FStar_Pervasives_Native.Some tysc ->
                                    ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                      tysc)
                                | FStar_Pervasives_Native.None  ->
                                    failwith "No type scheme")
                           | uu____2297 -> failwith "Impossible"  in
                         match uu____2248 with
                         | (exp,tysc) ->
                             ((let uu____2321 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug
                                      g1.FStar_Extraction_ML_UEnv.tcenv)
                                   (FStar_Options.Other "ExtractionReify")
                                  in
                               if uu____2321
                               then
                                 ((let uu____2323 =
                                     FStar_Extraction_ML_Code.string_of_mlty
                                       a_nm
                                       (FStar_Pervasives_Native.snd tysc)
                                      in
                                   FStar_Util.print1
                                     "Extracted action type: %s\n" uu____2323);
                                  FStar_List.iter
                                    (fun x  ->
                                       FStar_Util.print1 "and binders: %s\n"
                                         x)
                                    (FStar_Pervasives_Native.fst tysc))
                               else ());
                              extend_env g1 a_lid a_nm exp tysc)))))
              in
           let uu____2329 =
             let uu____2334 =
               extract_fv
                 (FStar_Pervasives_Native.snd
                    ed.FStar_Syntax_Syntax.return_repr)
                in
             match uu____2334 with
             | (return_tm,ty_sc) ->
                 let uu____2349 =
                   FStar_Extraction_ML_UEnv.monad_op_name ed "return"  in
                 (match uu____2349 with
                  | (return_nm,return_lid) ->
                      extend_env g return_lid return_nm return_tm ty_sc)
              in
           (match uu____2329 with
            | (g1,return_decl) ->
                let uu____2368 =
                  let uu____2373 =
                    extract_fv
                      (FStar_Pervasives_Native.snd
                         ed.FStar_Syntax_Syntax.bind_repr)
                     in
                  match uu____2373 with
                  | (bind_tm,ty_sc) ->
                      let uu____2388 =
                        FStar_Extraction_ML_UEnv.monad_op_name ed "bind"  in
                      (match uu____2388 with
                       | (bind_nm,bind_lid) ->
                           extend_env g1 bind_lid bind_nm bind_tm ty_sc)
                   in
                (match uu____2368 with
                 | (g2,bind_decl) ->
                     let uu____2407 =
                       FStar_Util.fold_map extract_action g2
                         ed.FStar_Syntax_Syntax.actions
                        in
                     (match uu____2407 with
                      | (g3,actions) ->
                          (g3,
                            (FStar_List.append [return_decl; bind_decl]
                               actions)))))
       | FStar_Syntax_Syntax.Sig_splice uu____2428 ->
           failwith "impossible: trying to extract splice"
       | FStar_Syntax_Syntax.Sig_new_effect uu____2441 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____2445,t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let uu____2453 =
             let uu____2454 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___384_2458  ->
                       match uu___384_2458 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____2459 -> false))
                in
             Prims.op_Negation uu____2454  in
           if uu____2453
           then (g, [])
           else
             (let uu____2469 = FStar_Syntax_Util.arrow_formals t  in
              match uu____2469 with
              | (bs,uu____2489) ->
                  let fv =
                    FStar_Syntax_Syntax.lid_as_fv lid
                      FStar_Syntax_Syntax.delta_constant
                      FStar_Pervasives_Native.None
                     in
                  let uu____2507 =
                    FStar_Syntax_Util.abs bs FStar_Syntax_Syntax.t_unit
                      FStar_Pervasives_Native.None
                     in
                  extract_typ_abbrev g fv quals attrs uu____2507)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____2509) when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____2519 =
             let uu____2528 =
               FStar_TypeChecker_Env.open_universes_in
                 g.FStar_Extraction_ML_UEnv.tcenv
                 lb.FStar_Syntax_Syntax.lbunivs
                 [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp]
                in
             match uu____2528 with
             | (tcenv,uu____2546,def_typ) ->
                 let uu____2552 = as_pair def_typ  in (tcenv, uu____2552)
              in
           (match uu____2519 with
            | (tcenv,(lbdef,lbtyp)) ->
                let lbtyp1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.UnfoldUntil
                      FStar_Syntax_Syntax.delta_constant] tcenv lbtyp
                   in
                let lbdef1 =
                  FStar_TypeChecker_Normalize.eta_expand_with_type tcenv
                    lbdef lbtyp1
                   in
                let uu____2576 =
                  FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                extract_typ_abbrev g uu____2576 quals
                  se.FStar_Syntax_Syntax.sigattrs lbdef1)
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____2578) ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____2589 =
             let uu____2596 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let
                    (lbs, FStar_Syntax_Util.exp_false_bool))
                 FStar_Pervasives_Native.None se.FStar_Syntax_Syntax.sigrng
                in
             FStar_Extraction_ML_Term.term_as_mlexpr g uu____2596  in
           (match uu____2589 with
            | (ml_let,uu____2612,uu____2613) ->
                (match ml_let.FStar_Extraction_ML_Syntax.expr with
                 | FStar_Extraction_ML_Syntax.MLE_Let
                     ((flavor,bindings),uu____2622) ->
                     let flags1 = FStar_List.choose flag_of_qual quals  in
                     let flags' = extract_metadata attrs  in
                     let uu____2639 =
                       FStar_List.fold_left2
                         (fun uu____2665  ->
                            fun ml_lb  ->
                              fun uu____2667  ->
                                match (uu____2665, uu____2667) with
                                | ((env,ml_lbs),{
                                                  FStar_Syntax_Syntax.lbname
                                                    = lbname;
                                                  FStar_Syntax_Syntax.lbunivs
                                                    = uu____2689;
                                                  FStar_Syntax_Syntax.lbtyp =
                                                    t;
                                                  FStar_Syntax_Syntax.lbeff =
                                                    uu____2691;
                                                  FStar_Syntax_Syntax.lbdef =
                                                    uu____2692;
                                                  FStar_Syntax_Syntax.lbattrs
                                                    = uu____2693;
                                                  FStar_Syntax_Syntax.lbpos =
                                                    uu____2694;_})
                                    ->
                                    let uu____2719 =
                                      FStar_All.pipe_right
                                        ml_lb.FStar_Extraction_ML_Syntax.mllb_meta
                                        (FStar_List.contains
                                           FStar_Extraction_ML_Syntax.Erased)
                                       in
                                    if uu____2719
                                    then (env, ml_lbs)
                                    else
                                      (let lb_lid =
                                         let uu____2732 =
                                           let uu____2735 =
                                             FStar_Util.right lbname  in
                                           uu____2735.FStar_Syntax_Syntax.fv_name
                                            in
                                         uu____2732.FStar_Syntax_Syntax.v  in
                                       let flags'' =
                                         let uu____2739 =
                                           let uu____2740 =
                                             FStar_Syntax_Subst.compress t
                                              in
                                           uu____2740.FStar_Syntax_Syntax.n
                                            in
                                         match uu____2739 with
                                         | FStar_Syntax_Syntax.Tm_arrow
                                             (uu____2745,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Comp
                                                             {
                                                               FStar_Syntax_Syntax.comp_univs
                                                                 = uu____2746;
                                                               FStar_Syntax_Syntax.effect_name
                                                                 = e;
                                                               FStar_Syntax_Syntax.result_typ
                                                                 = uu____2748;
                                                               FStar_Syntax_Syntax.effect_args
                                                                 = uu____2749;
                                                               FStar_Syntax_Syntax.flags
                                                                 = uu____2750;_};
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____2751;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____2752;_})
                                             when
                                             let uu____2781 =
                                               FStar_Ident.string_of_lid e
                                                in
                                             uu____2781 =
                                               "FStar.HyperStack.ST.StackInline"
                                             ->
                                             [FStar_Extraction_ML_Syntax.StackInline]
                                         | uu____2782 -> []  in
                                       let meta =
                                         FStar_List.append flags1
                                           (FStar_List.append flags' flags'')
                                          in
                                       let ml_lb1 =
                                         let uu___388_2787 = ml_lb  in
                                         {
                                           FStar_Extraction_ML_Syntax.mllb_name
                                             =
                                             (uu___388_2787.FStar_Extraction_ML_Syntax.mllb_name);
                                           FStar_Extraction_ML_Syntax.mllb_tysc
                                             =
                                             (uu___388_2787.FStar_Extraction_ML_Syntax.mllb_tysc);
                                           FStar_Extraction_ML_Syntax.mllb_add_unit
                                             =
                                             (uu___388_2787.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                           FStar_Extraction_ML_Syntax.mllb_def
                                             =
                                             (uu___388_2787.FStar_Extraction_ML_Syntax.mllb_def);
                                           FStar_Extraction_ML_Syntax.mllb_meta
                                             = meta;
                                           FStar_Extraction_ML_Syntax.print_typ
                                             =
                                             (uu___388_2787.FStar_Extraction_ML_Syntax.print_typ)
                                         }  in
                                       let uu____2788 =
                                         let uu____2793 =
                                           FStar_All.pipe_right quals
                                             (FStar_Util.for_some
                                                (fun uu___385_2798  ->
                                                   match uu___385_2798 with
                                                   | FStar_Syntax_Syntax.Projector
                                                       uu____2799 -> true
                                                   | uu____2804 -> false))
                                            in
                                         if uu____2793
                                         then
                                           let mname =
                                             let uu____2816 =
                                               mangle_projector_lid lb_lid
                                                in
                                             FStar_All.pipe_right uu____2816
                                               FStar_Extraction_ML_Syntax.mlpath_of_lident
                                              in
                                           let uu____2823 =
                                             let uu____2828 =
                                               FStar_Util.right lbname  in
                                             let uu____2829 =
                                               FStar_Util.must
                                                 ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                in
                                             FStar_Extraction_ML_UEnv.extend_fv'
                                               env uu____2828 mname
                                               uu____2829
                                               ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                               false
                                              in
                                           match uu____2823 with
                                           | (env1,uu____2835) ->
                                               (env1,
                                                 (let uu___389_2837 = ml_lb1
                                                     in
                                                  {
                                                    FStar_Extraction_ML_Syntax.mllb_name
                                                      =
                                                      (FStar_Pervasives_Native.snd
                                                         mname);
                                                    FStar_Extraction_ML_Syntax.mllb_tysc
                                                      =
                                                      (uu___389_2837.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                    FStar_Extraction_ML_Syntax.mllb_add_unit
                                                      =
                                                      (uu___389_2837.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                    FStar_Extraction_ML_Syntax.mllb_def
                                                      =
                                                      (uu___389_2837.FStar_Extraction_ML_Syntax.mllb_def);
                                                    FStar_Extraction_ML_Syntax.mllb_meta
                                                      =
                                                      (uu___389_2837.FStar_Extraction_ML_Syntax.mllb_meta);
                                                    FStar_Extraction_ML_Syntax.print_typ
                                                      =
                                                      (uu___389_2837.FStar_Extraction_ML_Syntax.print_typ)
                                                  }))
                                         else
                                           (let uu____2841 =
                                              let uu____2842 =
                                                let uu____2847 =
                                                  FStar_Util.must
                                                    ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                   in
                                                FStar_Extraction_ML_UEnv.extend_lb
                                                  env lbname t uu____2847
                                                  ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                                  false
                                                 in
                                              FStar_All.pipe_left
                                                FStar_Pervasives_Native.fst
                                                uu____2842
                                               in
                                            (uu____2841, ml_lb1))
                                          in
                                       match uu____2788 with
                                       | (g1,ml_lb2) ->
                                           (g1, (ml_lb2 :: ml_lbs)))) 
                         (g, []) bindings (FStar_Pervasives_Native.snd lbs)
                        in
                     (match uu____2639 with
                      | (g1,ml_lbs') ->
                          let uu____2878 =
                            let uu____2881 =
                              let uu____2884 =
                                let uu____2885 =
                                  FStar_Extraction_ML_Util.mlloc_of_range
                                    se.FStar_Syntax_Syntax.sigrng
                                   in
                                FStar_Extraction_ML_Syntax.MLM_Loc uu____2885
                                 in
                              [uu____2884;
                              FStar_Extraction_ML_Syntax.MLM_Let
                                (flavor, (FStar_List.rev ml_lbs'))]
                               in
                            let uu____2888 = maybe_register_plugin g1 se  in
                            FStar_List.append uu____2881 uu____2888  in
                          (g1, uu____2878))
                 | uu____2893 ->
                     let uu____2894 =
                       let uu____2895 =
                         FStar_Extraction_ML_Code.string_of_mlexpr
                           g.FStar_Extraction_ML_UEnv.currentModule ml_let
                          in
                       FStar_Util.format1
                         "Impossible: Translated a let to a non-let: %s"
                         uu____2895
                        in
                     failwith uu____2894))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____2903,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____2908 =
             (FStar_All.pipe_right quals
                (FStar_List.contains FStar_Syntax_Syntax.Assumption))
               &&
               (let uu____2912 =
                  FStar_TypeChecker_Util.must_erase_for_extraction
                    g.FStar_Extraction_ML_UEnv.tcenv t
                   in
                Prims.op_Negation uu____2912)
              in
           if uu____2908
           then
             let always_fail =
               let imp =
                 let uu____2923 = FStar_Syntax_Util.arrow_formals t  in
                 match uu____2923 with
                 | ([],t1) ->
                     let b =
                       let uu____2958 =
                         FStar_Syntax_Syntax.gen_bv "_"
                           FStar_Pervasives_Native.None t1
                          in
                       FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                         uu____2958
                        in
                     let uu____2963 = fail_exp lid t1  in
                     FStar_Syntax_Util.abs [b] uu____2963
                       FStar_Pervasives_Native.None
                 | (bs,t1) ->
                     let uu____2992 = fail_exp lid t1  in
                     FStar_Syntax_Util.abs bs uu____2992
                       FStar_Pervasives_Native.None
                  in
               let uu___390_2995 = se  in
               let uu____2996 =
                 let uu____2997 =
                   let uu____3004 =
                     let uu____3005 =
                       let uu____3008 =
                         let uu____3009 =
                           let uu____3014 =
                             FStar_Syntax_Syntax.lid_as_fv lid
                               FStar_Syntax_Syntax.delta_constant
                               FStar_Pervasives_Native.None
                              in
                           FStar_Util.Inr uu____3014  in
                         {
                           FStar_Syntax_Syntax.lbname = uu____3009;
                           FStar_Syntax_Syntax.lbunivs = [];
                           FStar_Syntax_Syntax.lbtyp = t;
                           FStar_Syntax_Syntax.lbeff =
                             FStar_Parser_Const.effect_ML_lid;
                           FStar_Syntax_Syntax.lbdef = imp;
                           FStar_Syntax_Syntax.lbattrs = [];
                           FStar_Syntax_Syntax.lbpos =
                             (imp.FStar_Syntax_Syntax.pos)
                         }  in
                       [uu____3008]  in
                     (false, uu____3005)  in
                   (uu____3004, [])  in
                 FStar_Syntax_Syntax.Sig_let uu____2997  in
               {
                 FStar_Syntax_Syntax.sigel = uu____2996;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___390_2995.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___390_2995.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___390_2995.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___390_2995.FStar_Syntax_Syntax.sigattrs)
               }  in
             let uu____3021 = extract_sig g always_fail  in
             (match uu____3021 with
              | (g1,mlm) ->
                  let uu____3040 =
                    FStar_Util.find_map quals
                      (fun uu___386_3045  ->
                         match uu___386_3045 with
                         | FStar_Syntax_Syntax.Discriminator l ->
                             FStar_Pervasives_Native.Some l
                         | uu____3049 -> FStar_Pervasives_Native.None)
                     in
                  (match uu____3040 with
                   | FStar_Pervasives_Native.Some l ->
                       let uu____3057 =
                         let uu____3060 =
                           let uu____3061 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng
                              in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____3061  in
                         let uu____3062 =
                           let uu____3065 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l
                              in
                           [uu____3065]  in
                         uu____3060 :: uu____3062  in
                       (g1, uu____3057)
                   | uu____3068 ->
                       let uu____3071 =
                         FStar_Util.find_map quals
                           (fun uu___387_3077  ->
                              match uu___387_3077 with
                              | FStar_Syntax_Syntax.Projector (l,uu____3081)
                                  -> FStar_Pervasives_Native.Some l
                              | uu____3082 -> FStar_Pervasives_Native.None)
                          in
                       (match uu____3071 with
                        | FStar_Pervasives_Native.Some uu____3089 -> (g1, [])
                        | uu____3092 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____3101 = FStar_Extraction_ML_Term.term_as_mlexpr g e  in
           (match uu____3101 with
            | (ml_main,uu____3115,uu____3116) ->
                let uu____3117 =
                  let uu____3120 =
                    let uu____3121 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng
                       in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____3121  in
                  [uu____3120; FStar_Extraction_ML_Syntax.MLM_Top ml_main]
                   in
                (g, uu____3117))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____3124 ->
           failwith "impossible -- removed by tc.fs"
       | FStar_Syntax_Syntax.Sig_assume uu____3131 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____3140 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____3143 -> (g, [])
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (FStar_Syntax_Util.process_pragma p se.FStar_Syntax_Syntax.sigrng;
            (g, [])))
  
let (extract_iface :
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.modul -> env_t) =
  fun g  ->
    fun m  ->
      let uu____3172 =
        FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____3172 FStar_Pervasives_Native.fst
  
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
      (let uu____3218 = FStar_Options.restore_cmd_line_options true  in
       let name =
         FStar_Extraction_ML_Syntax.mlpath_of_lident
           m.FStar_Syntax_Syntax.name
          in
       let g1 =
         let uu___391_3221 = g  in
         let uu____3222 =
           FStar_TypeChecker_Env.set_current_module
             g.FStar_Extraction_ML_UEnv.tcenv m.FStar_Syntax_Syntax.name
            in
         {
           FStar_Extraction_ML_UEnv.tcenv = uu____3222;
           FStar_Extraction_ML_UEnv.gamma =
             (uu___391_3221.FStar_Extraction_ML_UEnv.gamma);
           FStar_Extraction_ML_UEnv.tydefs =
             (uu___391_3221.FStar_Extraction_ML_UEnv.tydefs);
           FStar_Extraction_ML_UEnv.type_names =
             (uu___391_3221.FStar_Extraction_ML_UEnv.type_names);
           FStar_Extraction_ML_UEnv.currentModule = name
         }  in
       let uu____3223 =
         FStar_Util.fold_map extract_sig g1
           m.FStar_Syntax_Syntax.declarations
          in
       match uu____3223 with
       | (g2,sigs) ->
           let mlm = FStar_List.flatten sigs  in
           let is_kremlin =
             let uu____3252 = FStar_Options.codegen ()  in
             uu____3252 =
               (FStar_Pervasives_Native.Some FStar_Options.Kremlin)
              in
           let uu____3257 =
             (((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
                (is_kremlin ||
                   (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)))
               &&
               (FStar_Options.should_extract
                  (m.FStar_Syntax_Syntax.name).FStar_Ident.str)
              in
           if uu____3257
           then
             ((let uu____3265 =
                 FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name
                  in
               FStar_Util.print1 "Extracted module %s\n" uu____3265);
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
      let uu____3333 = FStar_Options.debug_any ()  in
      if uu____3333
      then
        let msg =
          let uu____3341 =
            FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name  in
          FStar_Util.format1 "Extracting module %s\n" uu____3341  in
        FStar_Util.measure_execution_time msg
          (fun uu____3349  -> extract' g m)
      else extract' g m
  