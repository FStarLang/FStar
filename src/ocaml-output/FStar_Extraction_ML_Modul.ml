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
                FStar_Syntax_Syntax.Delta_constant
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
  fun uu___69_153  ->
    match uu___69_153 with
    | a::b::[] -> (a, b)
    | uu____158 -> failwith "Expected a list with 2 elements"
  
let rec (extract_meta :
  FStar_Syntax_Syntax.term ->
    FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option)
  =
  fun x  ->
    let uu____172 = FStar_Syntax_Subst.compress x  in
    match uu____172 with
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
        FStar_Syntax_Syntax.pos = uu____176;
        FStar_Syntax_Syntax.vars = uu____177;_} ->
        let uu____180 =
          let uu____181 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____181  in
        (match uu____180 with
         | "FStar.Pervasives.PpxDerivingShow" ->
             FStar_Pervasives_Native.Some
               FStar_Extraction_ML_Syntax.PpxDerivingShow
         | "FStar.Pervasives.CInline" ->
             FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CInline
         | "FStar.Pervasives.Substitute" ->
             FStar_Pervasives_Native.Some
               FStar_Extraction_ML_Syntax.Substitute
         | "FStar.Pervasives.Gc" ->
             FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.GCType
         | uu____184 -> FStar_Pervasives_Native.None)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____186;
             FStar_Syntax_Syntax.vars = uu____187;_},({
                                                        FStar_Syntax_Syntax.n
                                                          =
                                                          FStar_Syntax_Syntax.Tm_constant
                                                          (FStar_Const.Const_string
                                                          (s,uu____189));
                                                        FStar_Syntax_Syntax.pos
                                                          = uu____190;
                                                        FStar_Syntax_Syntax.vars
                                                          = uu____191;_},uu____192)::[]);
        FStar_Syntax_Syntax.pos = uu____193;
        FStar_Syntax_Syntax.vars = uu____194;_} ->
        let uu____225 =
          let uu____226 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____226  in
        (match uu____225 with
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
         | uu____229 -> FStar_Pervasives_Native.None)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("KremlinPrivate",uu____230));
        FStar_Syntax_Syntax.pos = uu____231;
        FStar_Syntax_Syntax.vars = uu____232;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Private
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("c_inline",uu____235));
        FStar_Syntax_Syntax.pos = uu____236;
        FStar_Syntax_Syntax.vars = uu____237;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CInline
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("substitute",uu____240));
        FStar_Syntax_Syntax.pos = uu____241;
        FStar_Syntax_Syntax.vars = uu____242;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Substitute
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_meta (x1,uu____246);
        FStar_Syntax_Syntax.pos = uu____247;
        FStar_Syntax_Syntax.vars = uu____248;_} -> extract_meta x1
    | uu____255 -> FStar_Pervasives_Native.None
  
let (extract_metadata :
  FStar_Syntax_Syntax.term Prims.list ->
    FStar_Extraction_ML_Syntax.meta Prims.list)
  = fun metas  -> FStar_List.choose extract_meta metas 
let binders_as_mlty_binders :
  'Auu____273 .
    FStar_Extraction_ML_UEnv.env ->
      (FStar_Syntax_Syntax.bv,'Auu____273) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Extraction_ML_UEnv.env,Prims.string Prims.list)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bs  ->
      FStar_Util.fold_map
        (fun env1  ->
           fun uu____313  ->
             match uu____313 with
             | (bv,uu____323) ->
                 let uu____324 =
                   let uu____325 =
                     let uu____328 =
                       let uu____329 =
                         FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv  in
                       FStar_Extraction_ML_Syntax.MLTY_Var uu____329  in
                     FStar_Pervasives_Native.Some uu____328  in
                   FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____325  in
                 let uu____330 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv
                    in
                 (uu____324, uu____330)) env bs
  
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
              let uu____374 =
                let uu____375 = FStar_Syntax_Subst.compress def  in
                FStar_All.pipe_right uu____375 FStar_Syntax_Util.unmeta  in
              FStar_All.pipe_right uu____374 FStar_Syntax_Util.un_uinst  in
            let def2 =
              match def1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_abs uu____383 ->
                  FStar_Extraction_ML_Term.normalize_abs def1
              | uu____400 -> def1  in
            let uu____401 =
              match def2.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____424) ->
                  FStar_Syntax_Subst.open_term bs body
              | uu____445 -> ([], def2)  in
            match uu____401 with
            | (bs,body) ->
                let assumed =
                  FStar_Util.for_some
                    (fun uu___70_480  ->
                       match uu___70_480 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____481 -> false) quals
                   in
                let uu____482 = binders_as_mlty_binders env bs  in
                (match uu____482 with
                 | (env1,ml_bs) ->
                     let body1 =
                       let uu____502 =
                         FStar_Extraction_ML_Term.term_as_mlty env1 body  in
                       FStar_All.pipe_right uu____502
                         (FStar_Extraction_ML_Util.eraseTypeDeep
                            (FStar_Extraction_ML_Util.udelta_unfold env1))
                        in
                     let mangled_projector =
                       let uu____506 =
                         FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___71_511  ->
                                 match uu___71_511 with
                                 | FStar_Syntax_Syntax.Projector uu____512 ->
                                     true
                                 | uu____517 -> false))
                          in
                       if uu____506
                       then
                         let mname = mangle_projector_lid lid  in
                         FStar_Pervasives_Native.Some
                           ((mname.FStar_Ident.ident).FStar_Ident.idText)
                       else FStar_Pervasives_Native.None  in
                     let metadata = extract_metadata attrs  in
                     let td =
                       let uu____528 =
                         let uu____529 = lident_as_mlsymbol lid  in
                         (assumed, uu____529, mangled_projector, ml_bs,
                           metadata,
                           (FStar_Pervasives_Native.Some
                              (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1)))
                          in
                       [uu____528]  in
                     let def3 =
                       let uu____541 =
                         let uu____542 =
                           let uu____543 = FStar_Ident.range_of_lid lid  in
                           FStar_Extraction_ML_Util.mlloc_of_range uu____543
                            in
                         FStar_Extraction_ML_Syntax.MLM_Loc uu____542  in
                       [uu____541; FStar_Extraction_ML_Syntax.MLM_Ty td]  in
                     let env2 =
                       let uu____545 =
                         FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___72_549  ->
                                 match uu___72_549 with
                                 | FStar_Syntax_Syntax.Assumption  -> true
                                 | FStar_Syntax_Syntax.New  -> true
                                 | uu____550 -> false))
                          in
                       if uu____545
                       then FStar_Extraction_ML_UEnv.extend_type_name env1 fv
                       else FStar_Extraction_ML_UEnv.extend_tydef env1 fv td
                        in
                     (env2, def3))
  
type data_constructor =
  {
  dname: FStar_Ident.lident ;
  dtyp: FStar_Syntax_Syntax.typ }[@@deriving show]
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
  imetadata: FStar_Extraction_ML_Syntax.metadata }[@@deriving show]
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
    let uu____715 = FStar_Syntax_Print.lid_to_string i.iname  in
    let uu____716 = FStar_Syntax_Print.binders_to_string " " i.iparams  in
    let uu____717 = FStar_Syntax_Print.term_to_string i.ityp  in
    let uu____718 =
      let uu____719 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let uu____730 = FStar_Syntax_Print.lid_to_string d.dname  in
                let uu____731 =
                  let uu____732 = FStar_Syntax_Print.term_to_string d.dtyp
                     in
                  Prims.strcat " : " uu____732  in
                Prims.strcat uu____730 uu____731))
         in
      FStar_All.pipe_right uu____719 (FStar_String.concat "\n\t\t")  in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____715 uu____716 uu____717
      uu____718
  
let bundle_as_inductive_families :
  'Auu____745 .
    FStar_Extraction_ML_UEnv.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'Auu____745 ->
          FStar_Syntax_Syntax.attribute Prims.list ->
            (FStar_Extraction_ML_UEnv.env,inductive_family Prims.list)
              FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun attrs  ->
          let uu____780 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun se  ->
                   match se.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,_us,bs,t,_mut_i,datas) ->
                       let uu____827 = FStar_Syntax_Subst.open_term bs t  in
                       (match uu____827 with
                        | (bs1,t1) ->
                            let datas1 =
                              FStar_All.pipe_right ses
                                (FStar_List.collect
                                   (fun se1  ->
                                      match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_datacon
                                          (d,uu____866,t2,l',nparams,uu____870)
                                          when FStar_Ident.lid_equals l l' ->
                                          let uu____875 =
                                            FStar_Syntax_Util.arrow_formals
                                              t2
                                             in
                                          (match uu____875 with
                                           | (bs',body) ->
                                               let uu____908 =
                                                 FStar_Util.first_N
                                                   (FStar_List.length bs1)
                                                   bs'
                                                  in
                                               (match uu____908 with
                                                | (bs_params,rest) ->
                                                    let subst1 =
                                                      FStar_List.map2
                                                        (fun uu____979  ->
                                                           fun uu____980  ->
                                                             match (uu____979,
                                                                    uu____980)
                                                             with
                                                             | ((b',uu____998),
                                                                (b,uu____1000))
                                                                 ->
                                                                 let uu____1009
                                                                   =
                                                                   let uu____1016
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b  in
                                                                   (b',
                                                                    uu____1016)
                                                                    in
                                                                 FStar_Syntax_Syntax.NT
                                                                   uu____1009)
                                                        bs_params bs1
                                                       in
                                                    let t3 =
                                                      let uu____1022 =
                                                        let uu____1023 =
                                                          FStar_Syntax_Syntax.mk_Total
                                                            body
                                                           in
                                                        FStar_Syntax_Util.arrow
                                                          rest uu____1023
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____1022
                                                        (FStar_Syntax_Subst.subst
                                                           subst1)
                                                       in
                                                    [{ dname = d; dtyp = t3 }]))
                                      | uu____1024 -> []))
                               in
                            let metadata =
                              extract_metadata
                                (FStar_List.append
                                   se.FStar_Syntax_Syntax.sigattrs attrs)
                               in
                            let env2 =
                              let uu____1029 =
                                FStar_Syntax_Syntax.lid_as_fv l
                                  FStar_Syntax_Syntax.Delta_constant
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Extraction_ML_UEnv.extend_type_name env1
                                uu____1029
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
                   | uu____1032 -> (env1, [])) env ses
             in
          match uu____780 with
          | (env1,ifams) -> (env1, (FStar_List.flatten ifams))
  
type env_t = FStar_Extraction_ML_UEnv.env[@@deriving show]
let (extract_bundle :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t,FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun se  ->
      let extract_ctor ml_tyvars env1 ctor =
        let mlt =
          let uu____1118 =
            FStar_Extraction_ML_Term.term_as_mlty env1 ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env1) uu____1118
           in
        let steps =
          [FStar_TypeChecker_Normalize.Inlining;
          FStar_TypeChecker_Normalize.UnfoldUntil
            FStar_Syntax_Syntax.Delta_constant;
          FStar_TypeChecker_Normalize.EraseUniverses;
          FStar_TypeChecker_Normalize.AllowUnboundUniverses]  in
        let names1 =
          let uu____1125 =
            let uu____1126 =
              let uu____1129 =
                FStar_TypeChecker_Normalize.normalize steps
                  env1.FStar_Extraction_ML_UEnv.tcenv ctor.dtyp
                 in
              FStar_Syntax_Subst.compress uu____1129  in
            uu____1126.FStar_Syntax_Syntax.n  in
          match uu____1125 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,uu____1133) ->
              FStar_List.map
                (fun uu____1159  ->
                   match uu____1159 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____1165;
                        FStar_Syntax_Syntax.sort = uu____1166;_},uu____1167)
                       -> ppname.FStar_Ident.idText) bs
          | uu____1170 -> []  in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____1177 =
          let uu____1178 =
            FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
          FStar_Pervasives_Native.fst uu____1178  in
        let uu____1183 =
          let uu____1194 = lident_as_mlsymbol ctor.dname  in
          let uu____1195 =
            let uu____1202 = FStar_Extraction_ML_Util.argTypes mlt  in
            FStar_List.zip names1 uu____1202  in
          (uu____1194, uu____1195)  in
        (uu____1177, uu____1183)  in
      let extract_one_family env1 ind =
        let uu____1254 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____1254 with
        | (env2,vars) ->
            let uu____1289 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor vars) env2)
               in
            (match uu____1289 with
             | (env3,ctors) ->
                 let uu____1382 = FStar_Syntax_Util.arrow_formals ind.ityp
                    in
                 (match uu____1382 with
                  | (indices,uu____1418) ->
                      let ml_params =
                        let uu____1438 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____1457  ->
                                    let uu____1462 =
                                      FStar_Util.string_of_int i  in
                                    Prims.strcat "'dummyV" uu____1462))
                           in
                        FStar_List.append vars uu____1438  in
                      let tbody =
                        let uu____1464 =
                          FStar_Util.find_opt
                            (fun uu___73_1469  ->
                               match uu___73_1469 with
                               | FStar_Syntax_Syntax.RecordType uu____1470 ->
                                   true
                               | uu____1479 -> false) ind.iquals
                           in
                        match uu____1464 with
                        | FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____1490 = FStar_List.hd ctors  in
                            (match uu____1490 with
                             | (uu____1511,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id1  ->
                                        fun uu____1548  ->
                                          match uu____1548 with
                                          | (uu____1557,ty) ->
                                              let lid =
                                                FStar_Ident.lid_of_ids
                                                  (FStar_List.append ns [id1])
                                                 in
                                              let uu____1560 =
                                                lident_as_mlsymbol lid  in
                                              (uu____1560, ty)) ids c_ty
                                    in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____1561 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors
                         in
                      let uu____1564 =
                        let uu____1583 = lident_as_mlsymbol ind.iname  in
                        (false, uu____1583, FStar_Pervasives_Native.None,
                          ml_params, (ind.imetadata),
                          (FStar_Pervasives_Native.Some tbody))
                         in
                      (env3, uu____1564)))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____1617,t,uu____1619,uu____1620,uu____1621);
            FStar_Syntax_Syntax.sigrng = uu____1622;
            FStar_Syntax_Syntax.sigquals = uu____1623;
            FStar_Syntax_Syntax.sigmeta = uu____1624;
            FStar_Syntax_Syntax.sigattrs = uu____1625;_}::[],uu____1626),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____1643 = extract_ctor [] env { dname = l; dtyp = t }  in
          (match uu____1643 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____1689),quals) ->
          let uu____1703 =
            bundle_as_inductive_families env ses quals
              se.FStar_Syntax_Syntax.sigattrs
             in
          (match uu____1703 with
           | (env1,ifams) ->
               let uu____1724 =
                 FStar_Util.fold_map extract_one_family env1 ifams  in
               (match uu____1724 with
                | (env2,td) -> (env2, [FStar_Extraction_ML_Syntax.MLM_Ty td])))
      | uu____1745 -> failwith "Unexpected signature element"
  
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
      let uu____1777 =
        (let uu____1780 = FStar_Options.codegen ()  in
         uu____1780 <> (FStar_Pervasives_Native.Some FStar_Options.Plugin))
          ||
          (let uu____1786 =
             FStar_Syntax_Util.has_attribute se.FStar_Syntax_Syntax.sigattrs
               FStar_Parser_Const.plugin_attr
              in
           Prims.op_Negation uu____1786)
         in
      if uu____1777
      then []
      else
        (match se.FStar_Syntax_Syntax.sigel with
         | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
             let mk_registration lb =
               let fv =
                 let uu____1809 =
                   let uu____1812 =
                     FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                   uu____1812.FStar_Syntax_Syntax.fv_name  in
                 uu____1809.FStar_Syntax_Syntax.v  in
               let fv_t = lb.FStar_Syntax_Syntax.lbtyp  in
               let ml_name_str =
                 let uu____1817 =
                   let uu____1818 = FStar_Ident.string_of_lid fv  in
                   FStar_Extraction_ML_Syntax.MLC_String uu____1818  in
                 FStar_Extraction_ML_Syntax.MLE_Const uu____1817  in
               let uu____1819 =
                 FStar_Extraction_ML_Util.interpret_plugin_as_term_fun
                   g.FStar_Extraction_ML_UEnv.tcenv fv fv_t ml_name_str
                  in
               match uu____1819 with
               | FStar_Pervasives_Native.Some (interp,arity,plugin) ->
                   let register =
                     if plugin
                     then "FStar_Tactics_Native.register_plugin"
                     else "FStar_Tactics_Native.register_tactic"  in
                   let h =
                     let uu____1842 =
                       let uu____1843 =
                         let uu____1844 = FStar_Ident.lid_of_str register  in
                         FStar_Extraction_ML_Syntax.mlpath_of_lident
                           uu____1844
                          in
                       FStar_Extraction_ML_Syntax.MLE_Name uu____1843  in
                     FStar_All.pipe_left
                       (FStar_Extraction_ML_Syntax.with_ty
                          FStar_Extraction_ML_Syntax.MLTY_Top) uu____1842
                      in
                   let arity1 =
                     let uu____1846 =
                       let uu____1847 =
                         let uu____1858 = FStar_Util.string_of_int arity  in
                         (uu____1858, FStar_Pervasives_Native.None)  in
                       FStar_Extraction_ML_Syntax.MLC_Int uu____1847  in
                     FStar_Extraction_ML_Syntax.MLE_Const uu____1846  in
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
         | uu____1880 -> [])
  
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
           let uu____1907 = FStar_Syntax_Print.sigelt_to_string se  in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____1907);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____1914 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____1923 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____1940 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
           ->
           let extend_env g1 lid ml_name tm tysc =
             let uu____1988 =
               let uu____1993 =
                 FStar_Syntax_Syntax.lid_as_fv lid
                   FStar_Syntax_Syntax.Delta_equational
                   FStar_Pervasives_Native.None
                  in
               FStar_Extraction_ML_UEnv.extend_fv' g1 uu____1993 ml_name tysc
                 false false
                in
             match uu____1988 with
             | (g2,mangled_name) ->
                 ((let uu____2001 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          g2.FStar_Extraction_ML_UEnv.tcenv)
                       (FStar_Options.Other "ExtractionReify")
                      in
                   if uu____2001
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
             (let uu____2017 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify")
                 in
              if uu____2017
              then
                let uu____2018 = FStar_Syntax_Print.term_to_string tm  in
                FStar_Util.print1 "extract_fv term: %s\n" uu____2018
              else ());
             (let uu____2020 =
                let uu____2021 = FStar_Syntax_Subst.compress tm  in
                uu____2021.FStar_Syntax_Syntax.n  in
              match uu____2020 with
              | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____2029) ->
                  extract_fv tm1
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let mlp =
                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                     in
                  let uu____2036 =
                    let uu____2045 = FStar_Extraction_ML_UEnv.lookup_fv g fv
                       in
                    FStar_All.pipe_left FStar_Util.right uu____2045  in
                  (match uu____2036 with
                   | (uu____2102,uu____2103,tysc,uu____2105) ->
                       let uu____2106 =
                         FStar_All.pipe_left
                           (FStar_Extraction_ML_Syntax.with_ty
                              FStar_Extraction_ML_Syntax.MLTY_Top)
                           (FStar_Extraction_ML_Syntax.MLE_Name mlp)
                          in
                       (uu____2106, tysc))
              | uu____2107 -> failwith "Not an fv")
              in
           let extract_action g1 a =
             (let uu____2129 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g1.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify")
                 in
              if uu____2129
              then
                let uu____2130 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_typ
                   in
                let uu____2131 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_defn
                   in
                FStar_Util.print2 "Action type %s and term %s\n" uu____2130
                  uu____2131
              else ());
             (let uu____2133 = FStar_Extraction_ML_UEnv.action_name ed a  in
              match uu____2133 with
              | (a_nm,a_lid) ->
                  let lbname =
                    let uu____2149 =
                      FStar_Syntax_Syntax.new_bv
                        (FStar_Pervasives_Native.Some
                           ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                        FStar_Syntax_Syntax.tun
                       in
                    FStar_Util.Inl uu____2149  in
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
                  let uu____2173 =
                    FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb  in
                  (match uu____2173 with
                   | (a_let,uu____2185,ty) ->
                       ((let uu____2188 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug
                                g1.FStar_Extraction_ML_UEnv.tcenv)
                             (FStar_Options.Other "ExtractionReify")
                            in
                         if uu____2188
                         then
                           let uu____2189 =
                             FStar_Extraction_ML_Code.string_of_mlexpr a_nm
                               a_let
                              in
                           FStar_Util.print1 "Extracted action term: %s\n"
                             uu____2189
                         else ());
                        (let uu____2191 =
                           match a_let.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_Let
                               ((uu____2200,mllb::[]),uu____2202) ->
                               (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                                with
                                | FStar_Pervasives_Native.Some tysc ->
                                    ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                      tysc)
                                | FStar_Pervasives_Native.None  ->
                                    failwith "No type scheme")
                           | uu____2220 -> failwith "Impossible"  in
                         match uu____2191 with
                         | (exp,tysc) ->
                             ((let uu____2232 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug
                                      g1.FStar_Extraction_ML_UEnv.tcenv)
                                   (FStar_Options.Other "ExtractionReify")
                                  in
                               if uu____2232
                               then
                                 ((let uu____2234 =
                                     FStar_Extraction_ML_Code.string_of_mlty
                                       a_nm
                                       (FStar_Pervasives_Native.snd tysc)
                                      in
                                   FStar_Util.print1
                                     "Extracted action type: %s\n" uu____2234);
                                  FStar_List.iter
                                    (fun x  ->
                                       FStar_Util.print1 "and binders: %s\n"
                                         x)
                                    (FStar_Pervasives_Native.fst tysc))
                               else ());
                              extend_env g1 a_lid a_nm exp tysc)))))
              in
           let uu____2240 =
             let uu____2245 =
               extract_fv
                 (FStar_Pervasives_Native.snd
                    ed.FStar_Syntax_Syntax.return_repr)
                in
             match uu____2245 with
             | (return_tm,ty_sc) ->
                 let uu____2260 =
                   FStar_Extraction_ML_UEnv.monad_op_name ed "return"  in
                 (match uu____2260 with
                  | (return_nm,return_lid) ->
                      extend_env g return_lid return_nm return_tm ty_sc)
              in
           (match uu____2240 with
            | (g1,return_decl) ->
                let uu____2279 =
                  let uu____2284 =
                    extract_fv
                      (FStar_Pervasives_Native.snd
                         ed.FStar_Syntax_Syntax.bind_repr)
                     in
                  match uu____2284 with
                  | (bind_tm,ty_sc) ->
                      let uu____2299 =
                        FStar_Extraction_ML_UEnv.monad_op_name ed "bind"  in
                      (match uu____2299 with
                       | (bind_nm,bind_lid) ->
                           extend_env g1 bind_lid bind_nm bind_tm ty_sc)
                   in
                (match uu____2279 with
                 | (g2,bind_decl) ->
                     let uu____2318 =
                       FStar_Util.fold_map extract_action g2
                         ed.FStar_Syntax_Syntax.actions
                        in
                     (match uu____2318 with
                      | (g3,actions) ->
                          (g3,
                            (FStar_List.append [return_decl; bind_decl]
                               actions)))))
       | FStar_Syntax_Syntax.Sig_splice uu____2339 ->
           failwith "impossible: trying to extract splice"
       | FStar_Syntax_Syntax.Sig_new_effect uu____2352 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____2356,t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let uu____2364 =
             let uu____2365 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___74_2369  ->
                       match uu___74_2369 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____2370 -> false))
                in
             Prims.op_Negation uu____2365  in
           if uu____2364
           then (g, [])
           else
             (let uu____2380 = FStar_Syntax_Util.arrow_formals t  in
              match uu____2380 with
              | (bs,uu____2400) ->
                  let fv =
                    FStar_Syntax_Syntax.lid_as_fv lid
                      FStar_Syntax_Syntax.Delta_constant
                      FStar_Pervasives_Native.None
                     in
                  let uu____2418 =
                    FStar_Syntax_Util.abs bs FStar_Syntax_Syntax.t_unit
                      FStar_Pervasives_Native.None
                     in
                  extract_typ_abbrev g fv quals attrs uu____2418)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____2420) when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____2430 =
             let uu____2439 =
               FStar_TypeChecker_Env.open_universes_in
                 g.FStar_Extraction_ML_UEnv.tcenv
                 lb.FStar_Syntax_Syntax.lbunivs
                 [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp]
                in
             match uu____2439 with
             | (tcenv,uu____2457,def_typ) ->
                 let uu____2463 = as_pair def_typ  in (tcenv, uu____2463)
              in
           (match uu____2430 with
            | (tcenv,(lbdef,lbtyp)) ->
                let lbtyp1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.UnfoldUntil
                      FStar_Syntax_Syntax.Delta_constant] tcenv lbtyp
                   in
                let lbdef1 =
                  FStar_TypeChecker_Normalize.eta_expand_with_type tcenv
                    lbdef lbtyp1
                   in
                let uu____2487 =
                  FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                extract_typ_abbrev g uu____2487 quals
                  se.FStar_Syntax_Syntax.sigattrs lbdef1)
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____2489) ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____2500 =
             let uu____2507 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let
                    (lbs, FStar_Syntax_Util.exp_false_bool))
                 FStar_Pervasives_Native.None se.FStar_Syntax_Syntax.sigrng
                in
             FStar_Extraction_ML_Term.term_as_mlexpr g uu____2507  in
           (match uu____2500 with
            | (ml_let,uu____2523,uu____2524) ->
                (match ml_let.FStar_Extraction_ML_Syntax.expr with
                 | FStar_Extraction_ML_Syntax.MLE_Let
                     ((flavor,bindings),uu____2533) ->
                     let flags1 =
                       FStar_List.choose
                         (fun uu___75_2548  ->
                            match uu___75_2548 with
                            | FStar_Syntax_Syntax.Assumption  ->
                                FStar_Pervasives_Native.Some
                                  FStar_Extraction_ML_Syntax.Assumed
                            | FStar_Syntax_Syntax.Private  ->
                                FStar_Pervasives_Native.Some
                                  FStar_Extraction_ML_Syntax.Private
                            | FStar_Syntax_Syntax.NoExtract  ->
                                FStar_Pervasives_Native.Some
                                  FStar_Extraction_ML_Syntax.NoExtract
                            | uu____2551 -> FStar_Pervasives_Native.None)
                         quals
                        in
                     let flags' = extract_metadata attrs  in
                     let uu____2555 =
                       FStar_List.fold_left2
                         (fun uu____2581  ->
                            fun ml_lb  ->
                              fun uu____2583  ->
                                match (uu____2581, uu____2583) with
                                | ((env,ml_lbs),{
                                                  FStar_Syntax_Syntax.lbname
                                                    = lbname;
                                                  FStar_Syntax_Syntax.lbunivs
                                                    = uu____2605;
                                                  FStar_Syntax_Syntax.lbtyp =
                                                    t;
                                                  FStar_Syntax_Syntax.lbeff =
                                                    uu____2607;
                                                  FStar_Syntax_Syntax.lbdef =
                                                    uu____2608;
                                                  FStar_Syntax_Syntax.lbattrs
                                                    = uu____2609;
                                                  FStar_Syntax_Syntax.lbpos =
                                                    uu____2610;_})
                                    ->
                                    let uu____2635 =
                                      FStar_All.pipe_right
                                        ml_lb.FStar_Extraction_ML_Syntax.mllb_meta
                                        (FStar_List.contains
                                           FStar_Extraction_ML_Syntax.Erased)
                                       in
                                    if uu____2635
                                    then (env, ml_lbs)
                                    else
                                      (let lb_lid =
                                         let uu____2648 =
                                           let uu____2651 =
                                             FStar_Util.right lbname  in
                                           uu____2651.FStar_Syntax_Syntax.fv_name
                                            in
                                         uu____2648.FStar_Syntax_Syntax.v  in
                                       let flags'' =
                                         let uu____2655 =
                                           let uu____2656 =
                                             FStar_Syntax_Subst.compress t
                                              in
                                           uu____2656.FStar_Syntax_Syntax.n
                                            in
                                         match uu____2655 with
                                         | FStar_Syntax_Syntax.Tm_arrow
                                             (uu____2661,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Comp
                                                             {
                                                               FStar_Syntax_Syntax.comp_univs
                                                                 = uu____2662;
                                                               FStar_Syntax_Syntax.effect_name
                                                                 = e;
                                                               FStar_Syntax_Syntax.result_typ
                                                                 = uu____2664;
                                                               FStar_Syntax_Syntax.effect_args
                                                                 = uu____2665;
                                                               FStar_Syntax_Syntax.flags
                                                                 = uu____2666;_};
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____2667;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____2668;_})
                                             when
                                             let uu____2697 =
                                               FStar_Ident.string_of_lid e
                                                in
                                             uu____2697 =
                                               "FStar.HyperStack.ST.StackInline"
                                             ->
                                             [FStar_Extraction_ML_Syntax.StackInline]
                                         | uu____2698 -> []  in
                                       let meta =
                                         FStar_List.append flags1
                                           (FStar_List.append flags' flags'')
                                          in
                                       let ml_lb1 =
                                         let uu___79_2703 = ml_lb  in
                                         {
                                           FStar_Extraction_ML_Syntax.mllb_name
                                             =
                                             (uu___79_2703.FStar_Extraction_ML_Syntax.mllb_name);
                                           FStar_Extraction_ML_Syntax.mllb_tysc
                                             =
                                             (uu___79_2703.FStar_Extraction_ML_Syntax.mllb_tysc);
                                           FStar_Extraction_ML_Syntax.mllb_add_unit
                                             =
                                             (uu___79_2703.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                           FStar_Extraction_ML_Syntax.mllb_def
                                             =
                                             (uu___79_2703.FStar_Extraction_ML_Syntax.mllb_def);
                                           FStar_Extraction_ML_Syntax.mllb_meta
                                             = meta;
                                           FStar_Extraction_ML_Syntax.print_typ
                                             =
                                             (uu___79_2703.FStar_Extraction_ML_Syntax.print_typ)
                                         }  in
                                       let uu____2704 =
                                         let uu____2709 =
                                           FStar_All.pipe_right quals
                                             (FStar_Util.for_some
                                                (fun uu___76_2714  ->
                                                   match uu___76_2714 with
                                                   | FStar_Syntax_Syntax.Projector
                                                       uu____2715 -> true
                                                   | uu____2720 -> false))
                                            in
                                         if uu____2709
                                         then
                                           let mname =
                                             let uu____2726 =
                                               mangle_projector_lid lb_lid
                                                in
                                             FStar_All.pipe_right uu____2726
                                               FStar_Extraction_ML_Syntax.mlpath_of_lident
                                              in
                                           let uu____2727 =
                                             let uu____2732 =
                                               FStar_Util.right lbname  in
                                             let uu____2733 =
                                               FStar_Util.must
                                                 ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                in
                                             FStar_Extraction_ML_UEnv.extend_fv'
                                               env uu____2732 mname
                                               uu____2733
                                               ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                               false
                                              in
                                           match uu____2727 with
                                           | (env1,uu____2739) ->
                                               (env1,
                                                 (let uu___80_2741 = ml_lb1
                                                     in
                                                  {
                                                    FStar_Extraction_ML_Syntax.mllb_name
                                                      =
                                                      (FStar_Pervasives_Native.snd
                                                         mname);
                                                    FStar_Extraction_ML_Syntax.mllb_tysc
                                                      =
                                                      (uu___80_2741.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                    FStar_Extraction_ML_Syntax.mllb_add_unit
                                                      =
                                                      (uu___80_2741.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                    FStar_Extraction_ML_Syntax.mllb_def
                                                      =
                                                      (uu___80_2741.FStar_Extraction_ML_Syntax.mllb_def);
                                                    FStar_Extraction_ML_Syntax.mllb_meta
                                                      =
                                                      (uu___80_2741.FStar_Extraction_ML_Syntax.mllb_meta);
                                                    FStar_Extraction_ML_Syntax.print_typ
                                                      =
                                                      (uu___80_2741.FStar_Extraction_ML_Syntax.print_typ)
                                                  }))
                                         else
                                           (let uu____2745 =
                                              let uu____2746 =
                                                let uu____2751 =
                                                  FStar_Util.must
                                                    ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                   in
                                                FStar_Extraction_ML_UEnv.extend_lb
                                                  env lbname t uu____2751
                                                  ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                                  false
                                                 in
                                              FStar_All.pipe_left
                                                FStar_Pervasives_Native.fst
                                                uu____2746
                                               in
                                            (uu____2745, ml_lb1))
                                          in
                                       match uu____2704 with
                                       | (g1,ml_lb2) ->
                                           (g1, (ml_lb2 :: ml_lbs)))) 
                         (g, []) bindings (FStar_Pervasives_Native.snd lbs)
                        in
                     (match uu____2555 with
                      | (g1,ml_lbs') ->
                          let uu____2782 =
                            let uu____2785 =
                              let uu____2788 =
                                let uu____2789 =
                                  FStar_Extraction_ML_Util.mlloc_of_range
                                    se.FStar_Syntax_Syntax.sigrng
                                   in
                                FStar_Extraction_ML_Syntax.MLM_Loc uu____2789
                                 in
                              [uu____2788;
                              FStar_Extraction_ML_Syntax.MLM_Let
                                (flavor, (FStar_List.rev ml_lbs'))]
                               in
                            let uu____2792 = maybe_register_plugin g1 se  in
                            FStar_List.append uu____2785 uu____2792  in
                          (g1, uu____2782))
                 | uu____2797 ->
                     let uu____2798 =
                       let uu____2799 =
                         FStar_Extraction_ML_Code.string_of_mlexpr
                           g.FStar_Extraction_ML_UEnv.currentModule ml_let
                          in
                       FStar_Util.format1
                         "Impossible: Translated a let to a non-let: %s"
                         uu____2799
                        in
                     failwith uu____2798))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____2807,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____2812 =
             (FStar_All.pipe_right quals
                (FStar_List.contains FStar_Syntax_Syntax.Assumption))
               &&
               (let uu____2816 =
                  FStar_TypeChecker_Util.must_erase_for_extraction
                    g.FStar_Extraction_ML_UEnv.tcenv t
                   in
                Prims.op_Negation uu____2816)
              in
           if uu____2812
           then
             let always_fail =
               let imp =
                 let uu____2827 = FStar_Syntax_Util.arrow_formals t  in
                 match uu____2827 with
                 | ([],t1) ->
                     let b =
                       let uu____2862 =
                         FStar_Syntax_Syntax.gen_bv "_"
                           FStar_Pervasives_Native.None t1
                          in
                       FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                         uu____2862
                        in
                     let uu____2867 = fail_exp lid t1  in
                     FStar_Syntax_Util.abs [b] uu____2867
                       FStar_Pervasives_Native.None
                 | (bs,t1) ->
                     let uu____2896 = fail_exp lid t1  in
                     FStar_Syntax_Util.abs bs uu____2896
                       FStar_Pervasives_Native.None
                  in
               let uu___81_2899 = se  in
               let uu____2900 =
                 let uu____2901 =
                   let uu____2908 =
                     let uu____2909 =
                       let uu____2912 =
                         let uu____2913 =
                           let uu____2918 =
                             FStar_Syntax_Syntax.lid_as_fv lid
                               FStar_Syntax_Syntax.Delta_constant
                               FStar_Pervasives_Native.None
                              in
                           FStar_Util.Inr uu____2918  in
                         {
                           FStar_Syntax_Syntax.lbname = uu____2913;
                           FStar_Syntax_Syntax.lbunivs = [];
                           FStar_Syntax_Syntax.lbtyp = t;
                           FStar_Syntax_Syntax.lbeff =
                             FStar_Parser_Const.effect_ML_lid;
                           FStar_Syntax_Syntax.lbdef = imp;
                           FStar_Syntax_Syntax.lbattrs = [];
                           FStar_Syntax_Syntax.lbpos =
                             (imp.FStar_Syntax_Syntax.pos)
                         }  in
                       [uu____2912]  in
                     (false, uu____2909)  in
                   (uu____2908, [])  in
                 FStar_Syntax_Syntax.Sig_let uu____2901  in
               {
                 FStar_Syntax_Syntax.sigel = uu____2900;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___81_2899.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___81_2899.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___81_2899.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___81_2899.FStar_Syntax_Syntax.sigattrs)
               }  in
             let uu____2925 = extract_sig g always_fail  in
             (match uu____2925 with
              | (g1,mlm) ->
                  let uu____2944 =
                    FStar_Util.find_map quals
                      (fun uu___77_2949  ->
                         match uu___77_2949 with
                         | FStar_Syntax_Syntax.Discriminator l ->
                             FStar_Pervasives_Native.Some l
                         | uu____2953 -> FStar_Pervasives_Native.None)
                     in
                  (match uu____2944 with
                   | FStar_Pervasives_Native.Some l ->
                       let uu____2961 =
                         let uu____2964 =
                           let uu____2965 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng
                              in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____2965  in
                         let uu____2966 =
                           let uu____2969 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l
                              in
                           [uu____2969]  in
                         uu____2964 :: uu____2966  in
                       (g1, uu____2961)
                   | uu____2972 ->
                       let uu____2975 =
                         FStar_Util.find_map quals
                           (fun uu___78_2981  ->
                              match uu___78_2981 with
                              | FStar_Syntax_Syntax.Projector (l,uu____2985)
                                  -> FStar_Pervasives_Native.Some l
                              | uu____2986 -> FStar_Pervasives_Native.None)
                          in
                       (match uu____2975 with
                        | FStar_Pervasives_Native.Some uu____2993 -> (g1, [])
                        | uu____2996 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____3005 = FStar_Extraction_ML_Term.term_as_mlexpr g e  in
           (match uu____3005 with
            | (ml_main,uu____3019,uu____3020) ->
                let uu____3021 =
                  let uu____3024 =
                    let uu____3025 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng
                       in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____3025  in
                  [uu____3024; FStar_Extraction_ML_Syntax.MLM_Top ml_main]
                   in
                (g, uu____3021))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____3028 ->
           failwith "impossible -- removed by tc.fs"
       | FStar_Syntax_Syntax.Sig_assume uu____3035 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____3044 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____3047 -> (g, [])
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (FStar_Syntax_Util.process_pragma p se.FStar_Syntax_Syntax.sigrng;
            (g, [])))
  
let (extract_iface :
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.modul -> env_t) =
  fun g  ->
    fun m  ->
      let uu____3076 =
        FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____3076 FStar_Pervasives_Native.fst
  
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
      (let uu____3122 = FStar_Options.restore_cmd_line_options true  in
       let name =
         FStar_Extraction_ML_Syntax.mlpath_of_lident
           m.FStar_Syntax_Syntax.name
          in
       let g1 =
         let uu___82_3125 = g  in
         let uu____3126 =
           FStar_TypeChecker_Env.set_current_module
             g.FStar_Extraction_ML_UEnv.tcenv m.FStar_Syntax_Syntax.name
            in
         {
           FStar_Extraction_ML_UEnv.tcenv = uu____3126;
           FStar_Extraction_ML_UEnv.gamma =
             (uu___82_3125.FStar_Extraction_ML_UEnv.gamma);
           FStar_Extraction_ML_UEnv.tydefs =
             (uu___82_3125.FStar_Extraction_ML_UEnv.tydefs);
           FStar_Extraction_ML_UEnv.type_names =
             (uu___82_3125.FStar_Extraction_ML_UEnv.type_names);
           FStar_Extraction_ML_UEnv.currentModule = name
         }  in
       let uu____3127 =
         FStar_Util.fold_map extract_sig g1
           m.FStar_Syntax_Syntax.declarations
          in
       match uu____3127 with
       | (g2,sigs) ->
           let mlm = FStar_List.flatten sigs  in
           let is_kremlin =
             let uu____3156 = FStar_Options.codegen ()  in
             uu____3156 =
               (FStar_Pervasives_Native.Some FStar_Options.Kremlin)
              in
           let uu____3161 =
             (((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
                (is_kremlin ||
                   (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)))
               &&
               (FStar_Options.should_extract
                  (m.FStar_Syntax_Syntax.name).FStar_Ident.str)
              in
           if uu____3161
           then
             ((let uu____3169 =
                 FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name
                  in
               FStar_Util.print1 "Extracted module %s\n" uu____3169);
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
      let uu____3243 = FStar_Options.debug_any ()  in
      if uu____3243
      then
        let msg =
          let uu____3251 =
            FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name  in
          FStar_Util.format1 "Extracting module %s\n" uu____3251  in
        FStar_Util.measure_execution_time msg
          (fun uu____3259  -> extract' g m)
      else extract' g m
  