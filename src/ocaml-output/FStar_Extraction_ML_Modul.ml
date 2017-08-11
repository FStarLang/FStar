open Prims
let fail_exp :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun lid  ->
    fun t  ->
      let uu____11 =
        let uu____14 =
          let uu____15 =
            let uu____30 =
              FStar_Syntax_Syntax.fvar FStar_Parser_Const.failwith_lid
                FStar_Syntax_Syntax.Delta_constant
                FStar_Pervasives_Native.None
               in
            let uu____31 =
              let uu____34 = FStar_Syntax_Syntax.iarg t  in
              let uu____35 =
                let uu____38 =
                  let uu____39 =
                    let uu____40 =
                      let uu____43 =
                        let uu____44 =
                          let uu____45 =
                            let uu____52 =
                              let uu____53 =
                                let uu____54 =
                                  FStar_Syntax_Print.lid_to_string lid  in
                                Prims.strcat "Not yet implemented:" uu____54
                                 in
                              FStar_Bytes.string_as_unicode_bytes uu____53
                               in
                            (uu____52, FStar_Range.dummyRange)  in
                          FStar_Const.Const_string uu____45  in
                        FStar_Syntax_Syntax.Tm_constant uu____44  in
                      FStar_Syntax_Syntax.mk uu____43  in
                    uu____40 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____39  in
                [uu____38]  in
              uu____34 :: uu____35  in
            (uu____30, uu____31)  in
          FStar_Syntax_Syntax.Tm_app uu____15  in
        FStar_Syntax_Syntax.mk uu____14  in
      uu____11 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let mangle_projector_lid : FStar_Ident.lident -> FStar_Ident.lident =
  fun x  -> x 
let lident_as_mlsymbol :
  FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlsymbol =
  fun id  -> (id.FStar_Ident.ident).FStar_Ident.idText 
let as_pair :
  'Auu____75 .
    'Auu____75 Prims.list ->
      ('Auu____75,'Auu____75) FStar_Pervasives_Native.tuple2
  =
  fun uu___151_85  ->
    match uu___151_85 with
    | a::b::[] -> (a, b)
    | uu____90 -> failwith "Expected a list with 2 elements"
  
let rec extract_meta :
  FStar_Syntax_Syntax.term ->
    FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option
  =
  fun x  ->
    let uu____103 = FStar_Syntax_Subst.compress x  in
    match uu____103 with
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
        FStar_Syntax_Syntax.pos = uu____107;
        FStar_Syntax_Syntax.vars = uu____108;_} when
        let uu____111 =
          let uu____112 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____112  in
        uu____111 = "FStar.Pervasives.PpxDerivingShow" ->
        FStar_Pervasives_Native.Some
          FStar_Extraction_ML_Syntax.PpxDerivingShow
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
        FStar_Syntax_Syntax.pos = uu____114;
        FStar_Syntax_Syntax.vars = uu____115;_} when
        let uu____118 =
          let uu____119 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____119  in
        uu____118 = "FStar.Pervasives.CInline" ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CInline
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
        FStar_Syntax_Syntax.pos = uu____121;
        FStar_Syntax_Syntax.vars = uu____122;_} when
        let uu____125 =
          let uu____126 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____126  in
        uu____125 = "FStar.Pervasives.Substitute" ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Substitute
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
        FStar_Syntax_Syntax.pos = uu____128;
        FStar_Syntax_Syntax.vars = uu____129;_} when
        let uu____132 =
          let uu____133 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____133  in
        uu____132 = "FStar.Pervasives.Gc" ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.GCType
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____135;
             FStar_Syntax_Syntax.vars = uu____136;_},({
                                                        FStar_Syntax_Syntax.n
                                                          =
                                                          FStar_Syntax_Syntax.Tm_constant
                                                          (FStar_Const.Const_string
                                                          (data,uu____138));
                                                        FStar_Syntax_Syntax.pos
                                                          = uu____139;
                                                        FStar_Syntax_Syntax.vars
                                                          = uu____140;_},uu____141)::[]);
        FStar_Syntax_Syntax.pos = uu____142;
        FStar_Syntax_Syntax.vars = uu____143;_} when
        let uu____178 =
          let uu____179 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____179  in
        uu____178 = "FStar.Pervasives.PpxDerivingShowConstant" ->
        FStar_Pervasives_Native.Some
          (FStar_Extraction_ML_Syntax.PpxDerivingShowConstant
             (FStar_Util.string_of_unicode data))
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string (data,uu____181));
        FStar_Syntax_Syntax.pos = uu____182;
        FStar_Syntax_Syntax.vars = uu____183;_} when
        (FStar_Util.string_of_unicode data) = "c_inline" ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CInline
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string (data,uu____191));
        FStar_Syntax_Syntax.pos = uu____192;
        FStar_Syntax_Syntax.vars = uu____193;_} when
        (FStar_Util.string_of_unicode data) = "substitute" ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Substitute
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_meta (x1,uu____201);
        FStar_Syntax_Syntax.pos = uu____202;
        FStar_Syntax_Syntax.vars = uu____203;_} -> extract_meta x1
    | a ->
        ((let uu____212 = FStar_Syntax_Print.term_to_string a  in
          FStar_Util.print1_warning
            "Warning: unrecognized attribute (%s), valid attributes are `c_inline`, `substitute`, and `gc`."
            uu____212);
         FStar_Pervasives_Native.None)
  
let extract_metadata :
  FStar_Syntax_Syntax.term Prims.list ->
    FStar_Extraction_ML_Syntax.meta Prims.list
  = fun metas  -> FStar_List.choose extract_meta metas 
let binders_as_mlty_binders :
  'Auu____229 .
    FStar_Extraction_ML_UEnv.env ->
      (FStar_Syntax_Syntax.bv,'Auu____229) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Extraction_ML_UEnv.env,(Prims.string,Prims.int)
                                        FStar_Pervasives_Native.tuple2
                                        Prims.list)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bs  ->
      FStar_Util.fold_map
        (fun env1  ->
           fun uu____275  ->
             match uu____275 with
             | (bv,uu____289) ->
                 let uu____290 =
                   let uu____291 =
                     let uu____294 =
                       let uu____295 =
                         FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv  in
                       FStar_Extraction_ML_Syntax.MLTY_Var uu____295  in
                     FStar_Pervasives_Native.Some uu____294  in
                   FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____291  in
                 let uu____296 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv
                    in
                 (uu____290, uu____296)) env bs
  
let extract_typ_abbrev :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.term Prims.list ->
          FStar_Syntax_Syntax.term ->
            (FStar_Extraction_ML_UEnv.env,FStar_Extraction_ML_Syntax.mlmodule1
                                            Prims.list)
              FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun fv  ->
      fun quals  ->
        fun attrs  ->
          fun def  ->
            let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            let def1 =
              let uu____341 =
                let uu____342 = FStar_Syntax_Subst.compress def  in
                FStar_All.pipe_right uu____342 FStar_Syntax_Util.unmeta  in
              FStar_All.pipe_right uu____341 FStar_Syntax_Util.un_uinst  in
            let def2 =
              match def1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_abs uu____344 ->
                  FStar_Extraction_ML_Term.normalize_abs def1
              | uu____361 -> def1  in
            let uu____362 =
              match def2.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____373) ->
                  FStar_Syntax_Subst.open_term bs body
              | uu____394 -> ([], def2)  in
            match uu____362 with
            | (bs,body) ->
                let assumed =
                  FStar_Util.for_some
                    (fun uu___152_415  ->
                       match uu___152_415 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____416 -> false) quals
                   in
                let uu____417 = binders_as_mlty_binders env bs  in
                (match uu____417 with
                 | (env1,ml_bs) ->
                     let body1 =
                       let uu____449 =
                         FStar_Extraction_ML_Term.term_as_mlty env1 body  in
                       FStar_All.pipe_right uu____449
                         (FStar_Extraction_ML_Util.eraseTypeDeep
                            (FStar_Extraction_ML_Util.udelta_unfold env1))
                        in
                     let mangled_projector =
                       let uu____453 =
                         FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___153_458  ->
                                 match uu___153_458 with
                                 | FStar_Syntax_Syntax.Projector uu____459 ->
                                     true
                                 | uu____464 -> false))
                          in
                       if uu____453
                       then
                         let mname = mangle_projector_lid lid  in
                         FStar_Pervasives_Native.Some
                           ((mname.FStar_Ident.ident).FStar_Ident.idText)
                       else FStar_Pervasives_Native.None  in
                     let metadata = extract_metadata attrs  in
                     let td =
                       let uu____499 =
                         let uu____524 = lident_as_mlsymbol lid  in
                         (assumed, uu____524, mangled_projector, ml_bs,
                           metadata,
                           (FStar_Pervasives_Native.Some
                              (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1)))
                          in
                       [uu____499]  in
                     let def3 =
                       let uu____588 =
                         let uu____589 =
                           FStar_Extraction_ML_Util.mlloc_of_range
                             (FStar_Ident.range_of_lid lid)
                            in
                         FStar_Extraction_ML_Syntax.MLM_Loc uu____589  in
                       [uu____588; FStar_Extraction_ML_Syntax.MLM_Ty td]  in
                     let env2 =
                       let uu____591 =
                         FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___154_595  ->
                                 match uu___154_595 with
                                 | FStar_Syntax_Syntax.Assumption  -> true
                                 | FStar_Syntax_Syntax.New  -> true
                                 | uu____596 -> false))
                          in
                       if uu____591
                       then FStar_Extraction_ML_UEnv.extend_type_name env1 fv
                       else FStar_Extraction_ML_UEnv.extend_tydef env1 fv td
                        in
                     (env2, def3))
  
type data_constructor =
  {
  dname: FStar_Ident.lident ;
  dtyp: FStar_Syntax_Syntax.typ }
let __proj__Mkdata_constructor__item__dname :
  data_constructor -> FStar_Ident.lident =
  fun projectee  ->
    match projectee with
    | { dname = __fname__dname; dtyp = __fname__dtyp;_} -> __fname__dname
  
let __proj__Mkdata_constructor__item__dtyp :
  data_constructor -> FStar_Syntax_Syntax.typ =
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
let __proj__Mkinductive_family__item__iname :
  inductive_family -> FStar_Ident.lident =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; imetadata = __fname__imetadata;_} ->
        __fname__iname
  
let __proj__Mkinductive_family__item__iparams :
  inductive_family -> FStar_Syntax_Syntax.binders =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; imetadata = __fname__imetadata;_} ->
        __fname__iparams
  
let __proj__Mkinductive_family__item__ityp :
  inductive_family -> FStar_Syntax_Syntax.term =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; imetadata = __fname__imetadata;_} ->
        __fname__ityp
  
let __proj__Mkinductive_family__item__idatas :
  inductive_family -> data_constructor Prims.list =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; imetadata = __fname__imetadata;_} ->
        __fname__idatas
  
let __proj__Mkinductive_family__item__iquals :
  inductive_family -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; imetadata = __fname__imetadata;_} ->
        __fname__iquals
  
let __proj__Mkinductive_family__item__imetadata :
  inductive_family -> FStar_Extraction_ML_Syntax.metadata =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; imetadata = __fname__imetadata;_} ->
        __fname__imetadata
  
let print_ifamily : inductive_family -> Prims.unit =
  fun i  ->
    let uu____744 = FStar_Syntax_Print.lid_to_string i.iname  in
    let uu____745 = FStar_Syntax_Print.binders_to_string " " i.iparams  in
    let uu____746 = FStar_Syntax_Print.term_to_string i.ityp  in
    let uu____747 =
      let uu____748 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let uu____759 = FStar_Syntax_Print.lid_to_string d.dname  in
                let uu____760 =
                  let uu____761 = FStar_Syntax_Print.term_to_string d.dtyp
                     in
                  Prims.strcat " : " uu____761  in
                Prims.strcat uu____759 uu____760))
         in
      FStar_All.pipe_right uu____748 (FStar_String.concat "\n\t\t")  in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____744 uu____745 uu____746
      uu____747
  
let bundle_as_inductive_families :
  'Auu____774 .
    FStar_Extraction_ML_UEnv.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'Auu____774 ->
          FStar_Syntax_Syntax.attribute Prims.list ->
            (FStar_Extraction_ML_UEnv.env,inductive_family Prims.list)
              FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun attrs  ->
          let uu____805 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun se  ->
                   match se.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,_us,bs,t,_mut_i,datas) ->
                       let uu____852 = FStar_Syntax_Subst.open_term bs t  in
                       (match uu____852 with
                        | (bs1,t1) ->
                            let datas1 =
                              FStar_All.pipe_right ses
                                (FStar_List.collect
                                   (fun se1  ->
                                      match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_datacon
                                          (d,uu____891,t2,l',nparams,uu____895)
                                          when FStar_Ident.lid_equals l l' ->
                                          let uu____900 =
                                            FStar_Syntax_Util.arrow_formals
                                              t2
                                             in
                                          (match uu____900 with
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
                                                        (fun uu____1004  ->
                                                           fun uu____1005  ->
                                                             match (uu____1004,
                                                                    uu____1005)
                                                             with
                                                             | ((b',uu____1023),
                                                                (b,uu____1025))
                                                                 ->
                                                                 let uu____1034
                                                                   =
                                                                   let uu____1041
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b  in
                                                                   (b',
                                                                    uu____1041)
                                                                    in
                                                                 FStar_Syntax_Syntax.NT
                                                                   uu____1034)
                                                        bs_params bs1
                                                       in
                                                    let t3 =
                                                      let uu____1043 =
                                                        let uu____1046 =
                                                          FStar_Syntax_Syntax.mk_Total
                                                            body
                                                           in
                                                        FStar_Syntax_Util.arrow
                                                          rest uu____1046
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____1043
                                                        (FStar_Syntax_Subst.subst
                                                           subst1)
                                                       in
                                                    [{ dname = d; dtyp = t3 }]))
                                      | uu____1051 -> []))
                               in
                            let metadata =
                              extract_metadata
                                (FStar_List.append
                                   se.FStar_Syntax_Syntax.sigattrs attrs)
                               in
                            let env2 =
                              let uu____1056 =
                                FStar_Syntax_Syntax.lid_as_fv l
                                  FStar_Syntax_Syntax.Delta_constant
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Extraction_ML_UEnv.extend_type_name env1
                                uu____1056
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
                   | uu____1059 -> (env1, [])) env ses
             in
          match uu____805 with
          | (env1,ifams) -> (env1, (FStar_List.flatten ifams))
  
type env_t = FStar_Extraction_ML_UEnv.env
let extract_bundle :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t,FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let extract_ctor ml_tyvars env1 ctor =
        let mlt =
          let uu____1145 =
            FStar_Extraction_ML_Term.term_as_mlty env1 ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env1) uu____1145
           in
        let steps =
          [FStar_TypeChecker_Normalize.Inlining;
          FStar_TypeChecker_Normalize.UnfoldUntil
            FStar_Syntax_Syntax.Delta_constant;
          FStar_TypeChecker_Normalize.EraseUniverses;
          FStar_TypeChecker_Normalize.AllowUnboundUniverses]  in
        let names1 =
          let uu____1152 =
            let uu____1153 =
              let uu____1156 =
                FStar_TypeChecker_Normalize.normalize steps
                  env1.FStar_Extraction_ML_UEnv.tcenv ctor.dtyp
                 in
              FStar_Syntax_Subst.compress uu____1156  in
            uu____1153.FStar_Syntax_Syntax.n  in
          match uu____1152 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,uu____1160) ->
              FStar_List.map
                (fun uu____1186  ->
                   match uu____1186 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____1192;
                        FStar_Syntax_Syntax.sort = uu____1193;_},uu____1194)
                       -> ppname.FStar_Ident.idText) bs
          | uu____1197 -> []  in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____1216 =
          let uu____1217 =
            FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
          FStar_Pervasives_Native.fst uu____1217  in
        let uu____1222 =
          let uu____1233 = lident_as_mlsymbol ctor.dname  in
          let uu____1234 =
            let uu____1241 = FStar_Extraction_ML_Util.argTypes mlt  in
            FStar_List.zip names1 uu____1241  in
          (uu____1233, uu____1234)  in
        (uu____1216, uu____1222)  in
      let extract_one_family env1 ind =
        let uu____1293 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____1293 with
        | (env2,vars) ->
            let uu____1344 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor vars) env2)
               in
            (match uu____1344 with
             | (env3,ctors) ->
                 let uu____1441 = FStar_Syntax_Util.arrow_formals ind.ityp
                    in
                 (match uu____1441 with
                  | (indices,uu____1481) ->
                      let ml_params =
                        let uu____1505 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____1536  ->
                                    let uu____1541 =
                                      let uu____1542 =
                                        FStar_Util.string_of_int i  in
                                      Prims.strcat "'dummyV" uu____1542  in
                                    (uu____1541, (Prims.parse_int "0"))))
                           in
                        FStar_List.append vars uu____1505  in
                      let tbody =
                        let uu____1548 =
                          FStar_Util.find_opt
                            (fun uu___155_1553  ->
                               match uu___155_1553 with
                               | FStar_Syntax_Syntax.RecordType uu____1554 ->
                                   true
                               | uu____1563 -> false) ind.iquals
                           in
                        match uu____1548 with
                        | FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____1574 = FStar_List.hd ctors  in
                            (match uu____1574 with
                             | (uu____1595,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id  ->
                                        fun uu____1634  ->
                                          match uu____1634 with
                                          | (uu____1643,ty) ->
                                              let lid =
                                                FStar_Ident.lid_of_ids
                                                  (FStar_List.append ns [id])
                                                 in
                                              let uu____1646 =
                                                lident_as_mlsymbol lid  in
                                              (uu____1646, ty)) ids c_ty
                                    in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____1647 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors
                         in
                      let uu____1650 =
                        let uu____1673 = lident_as_mlsymbol ind.iname  in
                        (false, uu____1673, FStar_Pervasives_Native.None,
                          ml_params, (ind.imetadata),
                          (FStar_Pervasives_Native.Some tbody))
                         in
                      (env3, uu____1650)))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____1715,t,uu____1717,uu____1718,uu____1719);
            FStar_Syntax_Syntax.sigrng = uu____1720;
            FStar_Syntax_Syntax.sigquals = uu____1721;
            FStar_Syntax_Syntax.sigmeta = uu____1722;
            FStar_Syntax_Syntax.sigattrs = uu____1723;_}::[],uu____1724),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____1741 = extract_ctor [] env { dname = l; dtyp = t }  in
          (match uu____1741 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____1791),quals) ->
          let uu____1805 =
            bundle_as_inductive_families env ses quals
              se.FStar_Syntax_Syntax.sigattrs
             in
          (match uu____1805 with
           | (env1,ifams) ->
               let uu____1826 =
                 FStar_Util.fold_map extract_one_family env1 ifams  in
               (match uu____1826 with
                | (env2,td) -> (env2, [FStar_Extraction_ML_Syntax.MLM_Ty td])))
      | uu____1935 -> failwith "Unexpected signature element"
  
let rec extract_sig :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t,FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun g  ->
    fun se  ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u  ->
           let uu____1972 = FStar_Syntax_Print.sigelt_to_string se  in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____1972);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____1979 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____1988 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____2005 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
           ->
           let extend_env g1 lid ml_name tm tysc =
             let uu____2043 =
               let uu____2048 =
                 FStar_Syntax_Syntax.lid_as_fv lid
                   FStar_Syntax_Syntax.Delta_equational
                   FStar_Pervasives_Native.None
                  in
               FStar_Extraction_ML_UEnv.extend_fv' g1 uu____2048 ml_name tysc
                 false false
                in
             match uu____2043 with
             | (g2,mangled_name) ->
                 ((let uu____2056 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          g2.FStar_Extraction_ML_UEnv.tcenv)
                       (FStar_Options.Other "ExtractionReify")
                      in
                   if uu____2056
                   then
                     FStar_Util.print1 "Mangled name: %s\n"
                       (FStar_Pervasives_Native.fst mangled_name)
                   else ());
                  (let lb =
                     {
                       FStar_Extraction_ML_Syntax.mllb_name = mangled_name;
                       FStar_Extraction_ML_Syntax.mllb_tysc =
                         FStar_Pervasives_Native.None;
                       FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                       FStar_Extraction_ML_Syntax.mllb_def = tm;
                       FStar_Extraction_ML_Syntax.print_typ = false
                     }  in
                   (g2,
                     (FStar_Extraction_ML_Syntax.MLM_Let
                        (FStar_Extraction_ML_Syntax.NonRec, [], [lb])))))
              in
           let rec extract_fv tm =
             (let uu____2072 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify")
                 in
              if uu____2072
              then
                let uu____2073 = FStar_Syntax_Print.term_to_string tm  in
                FStar_Util.print1 "extract_fv term: %s\n" uu____2073
              else ());
             (let uu____2075 =
                let uu____2076 = FStar_Syntax_Subst.compress tm  in
                uu____2076.FStar_Syntax_Syntax.n  in
              match uu____2075 with
              | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____2084) ->
                  extract_fv tm1
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let mlp =
                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                     in
                  let uu____2091 =
                    let uu____2100 = FStar_Extraction_ML_UEnv.lookup_fv g fv
                       in
                    FStar_All.pipe_left FStar_Util.right uu____2100  in
                  (match uu____2091 with
                   | (uu____2157,uu____2158,tysc,uu____2160) ->
                       let uu____2161 =
                         FStar_All.pipe_left
                           (FStar_Extraction_ML_Syntax.with_ty
                              FStar_Extraction_ML_Syntax.MLTY_Top)
                           (FStar_Extraction_ML_Syntax.MLE_Name mlp)
                          in
                       (uu____2161, tysc))
              | uu____2162 -> failwith "Not an fv")
              in
           let extract_action g1 a =
             (let uu____2188 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g1.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify")
                 in
              if uu____2188
              then
                let uu____2189 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_typ
                   in
                let uu____2190 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_defn
                   in
                FStar_Util.print2 "Action type %s and term %s\n" uu____2189
                  uu____2190
              else ());
             (let uu____2192 = FStar_Extraction_ML_UEnv.action_name ed a  in
              match uu____2192 with
              | (a_nm,a_lid) ->
                  let lbname =
                    let uu____2208 =
                      FStar_Syntax_Syntax.new_bv
                        (FStar_Pervasives_Native.Some
                           ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                        FStar_Syntax_Syntax.tun
                       in
                    FStar_Util.Inl uu____2208  in
                  let lb =
                    FStar_Syntax_Syntax.mk_lb
                      (lbname, (a.FStar_Syntax_Syntax.action_univs),
                        FStar_Parser_Const.effect_Tot_lid,
                        (a.FStar_Syntax_Syntax.action_typ),
                        (a.FStar_Syntax_Syntax.action_defn))
                     in
                  let lbs = (false, [lb])  in
                  let action_lb =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_let
                         (lbs, FStar_Syntax_Util.exp_false_bool))
                      FStar_Pervasives_Native.None
                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                     in
                  let uu____2234 =
                    FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb  in
                  (match uu____2234 with
                   | (a_let,uu____2246,ty) ->
                       ((let uu____2249 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug
                                g1.FStar_Extraction_ML_UEnv.tcenv)
                             (FStar_Options.Other "ExtractionReify")
                            in
                         if uu____2249
                         then
                           let uu____2250 =
                             FStar_Extraction_ML_Code.string_of_mlexpr a_nm
                               a_let
                              in
                           FStar_Util.print1 "Extracted action term: %s\n"
                             uu____2250
                         else ());
                        (let uu____2252 =
                           match a_let.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_Let
                               ((uu____2261,uu____2262,mllb::[]),uu____2264)
                               ->
                               (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                                with
                                | FStar_Pervasives_Native.Some tysc ->
                                    ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                      tysc)
                                | FStar_Pervasives_Native.None  ->
                                    failwith "No type scheme")
                           | uu____2284 -> failwith "Impossible"  in
                         match uu____2252 with
                         | (exp,tysc) ->
                             ((let uu____2296 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug
                                      g1.FStar_Extraction_ML_UEnv.tcenv)
                                   (FStar_Options.Other "ExtractionReify")
                                  in
                               if uu____2296
                               then
                                 ((let uu____2298 =
                                     FStar_Extraction_ML_Code.string_of_mlty
                                       a_nm
                                       (FStar_Pervasives_Native.snd tysc)
                                      in
                                   FStar_Util.print1
                                     "Extracted action type: %s\n" uu____2298);
                                  FStar_List.iter
                                    (fun x  ->
                                       FStar_Util.print1 "and binders: %s\n"
                                         (FStar_Pervasives_Native.fst x))
                                    (FStar_Pervasives_Native.fst tysc))
                               else ());
                              extend_env g1 a_lid a_nm exp tysc)))))
              in
           let uu____2310 =
             let uu____2315 =
               extract_fv
                 (FStar_Pervasives_Native.snd
                    ed.FStar_Syntax_Syntax.return_repr)
                in
             match uu____2315 with
             | (return_tm,ty_sc) ->
                 let uu____2328 =
                   FStar_Extraction_ML_UEnv.monad_op_name ed "return"  in
                 (match uu____2328 with
                  | (return_nm,return_lid) ->
                      extend_env g return_lid return_nm return_tm ty_sc)
              in
           (match uu____2310 with
            | (g1,return_decl) ->
                let uu____2347 =
                  let uu____2352 =
                    extract_fv
                      (FStar_Pervasives_Native.snd
                         ed.FStar_Syntax_Syntax.bind_repr)
                     in
                  match uu____2352 with
                  | (bind_tm,ty_sc) ->
                      let uu____2365 =
                        FStar_Extraction_ML_UEnv.monad_op_name ed "bind"  in
                      (match uu____2365 with
                       | (bind_nm,bind_lid) ->
                           extend_env g1 bind_lid bind_nm bind_tm ty_sc)
                   in
                (match uu____2347 with
                 | (g2,bind_decl) ->
                     let uu____2384 =
                       FStar_Util.fold_map extract_action g2
                         ed.FStar_Syntax_Syntax.actions
                        in
                     (match uu____2384 with
                      | (g3,actions) ->
                          (g3,
                            (FStar_List.append [return_decl; bind_decl]
                               actions)))))
       | FStar_Syntax_Syntax.Sig_new_effect uu____2405 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____2409,t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let uu____2417 =
             let uu____2418 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___156_2422  ->
                       match uu___156_2422 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____2423 -> false))
                in
             Prims.op_Negation uu____2418  in
           if uu____2417
           then (g, [])
           else
             (let uu____2433 = FStar_Syntax_Util.arrow_formals t  in
              match uu____2433 with
              | (bs,uu____2453) ->
                  let fv =
                    FStar_Syntax_Syntax.lid_as_fv lid
                      FStar_Syntax_Syntax.Delta_constant
                      FStar_Pervasives_Native.None
                     in
                  let uu____2471 =
                    FStar_Syntax_Util.abs bs FStar_Syntax_Syntax.t_unit
                      FStar_Pervasives_Native.None
                     in
                  extract_typ_abbrev g fv quals attrs uu____2471)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____2473) when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____2489 =
             let uu____2498 =
               FStar_TypeChecker_Env.open_universes_in
                 g.FStar_Extraction_ML_UEnv.tcenv
                 lb.FStar_Syntax_Syntax.lbunivs
                 [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp]
                in
             match uu____2498 with
             | (tcenv,uu____2522,def_typ) ->
                 let uu____2528 = as_pair def_typ  in (tcenv, uu____2528)
              in
           (match uu____2489 with
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
                let uu____2552 =
                  FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                extract_typ_abbrev g uu____2552 quals
                  se.FStar_Syntax_Syntax.sigattrs lbdef1)
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____2554) ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let elet =
             FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_let
                  (lbs, FStar_Syntax_Util.exp_false_bool))
               FStar_Pervasives_Native.None se.FStar_Syntax_Syntax.sigrng
              in
           let tactic_registration_decl =
             let is_tactic_decl tac_lid h =
               match h.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_uinst (h',uu____2581) ->
                   let uu____2586 =
                     let uu____2587 = FStar_Syntax_Subst.compress h'  in
                     uu____2587.FStar_Syntax_Syntax.n  in
                   (match uu____2586 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.tactic_lid
                        ->
                        let uu____2591 =
                          let uu____2592 =
                            FStar_Extraction_ML_Syntax.string_of_mlpath
                              g.FStar_Extraction_ML_UEnv.currentModule
                             in
                          FStar_Util.starts_with uu____2592 "FStar.Tactics"
                           in
                        Prims.op_Negation uu____2591
                    | uu____2593 -> false)
               | uu____2594 -> false  in
             let mk_registration tac_lid assm_lid t bs =
               let h =
                 let uu____2621 =
                   let uu____2622 =
                     let uu____2623 =
                       FStar_Ident.lid_of_str
                         "FStar_Tactics_Native.register_tactic"
                        in
                     FStar_Extraction_ML_Syntax.mlpath_of_lident uu____2623
                      in
                   FStar_Extraction_ML_Syntax.MLE_Name uu____2622  in
                 FStar_All.pipe_left
                   (FStar_Extraction_ML_Syntax.with_ty
                      FStar_Extraction_ML_Syntax.MLTY_Top) uu____2621
                  in
               let lid_arg =
                 let uu____2625 =
                   let uu____2626 = FStar_Ident.string_of_lid assm_lid  in
                   FStar_Extraction_ML_Syntax.MLC_String uu____2626  in
                 FStar_Extraction_ML_Syntax.MLE_Const uu____2625  in
               let tac_arity = FStar_List.length bs  in
               let arity =
                 let uu____2633 =
                   let uu____2634 =
                     let uu____2635 =
                       FStar_Util.string_of_int
                         (tac_arity + (Prims.parse_int "1"))
                        in
                     FStar_Ident.lid_of_str uu____2635  in
                   FStar_Extraction_ML_Syntax.mlpath_of_lident uu____2634  in
                 FStar_Extraction_ML_Syntax.MLE_Name uu____2633  in
               let tac_interpretation =
                 FStar_Extraction_ML_Util.mk_interpretation_fun tac_lid
                   lid_arg t bs
                  in
               let app =
                 let uu____2644 =
                   let uu____2645 =
                     let uu____2652 =
                       FStar_List.map
                         (FStar_Extraction_ML_Syntax.with_ty
                            FStar_Extraction_ML_Syntax.MLTY_Top)
                         [lid_arg; arity; tac_interpretation]
                        in
                     (h, uu____2652)  in
                   FStar_Extraction_ML_Syntax.MLE_App uu____2645  in
                 FStar_All.pipe_left
                   (FStar_Extraction_ML_Syntax.with_ty
                      FStar_Extraction_ML_Syntax.MLTY_Top) uu____2644
                  in
               FStar_Extraction_ML_Syntax.MLM_Top app  in
             match FStar_Pervasives_Native.snd lbs with
             | hd1::[] ->
                 let uu____2662 =
                   FStar_Syntax_Util.arrow_formals_comp
                     hd1.FStar_Syntax_Syntax.lbtyp
                    in
                 (match uu____2662 with
                  | (bs,comp) ->
                      let t = FStar_Syntax_Util.comp_result comp  in
                      let uu____2692 =
                        let uu____2693 = FStar_Syntax_Subst.compress t  in
                        uu____2693.FStar_Syntax_Syntax.n  in
                      (match uu____2692 with
                       | FStar_Syntax_Syntax.Tm_app (h,args) ->
                           let h1 = FStar_Syntax_Subst.compress h  in
                           let tac_lid =
                             let uu____2722 =
                               let uu____2725 =
                                 FStar_Util.right
                                   hd1.FStar_Syntax_Syntax.lbname
                                  in
                               uu____2725.FStar_Syntax_Syntax.fv_name  in
                             uu____2722.FStar_Syntax_Syntax.v  in
                           let assm_lid =
                             let uu____2727 =
                               FStar_All.pipe_left FStar_Ident.id_of_text
                                 (Prims.strcat "__"
                                    (tac_lid.FStar_Ident.ident).FStar_Ident.idText)
                                in
                             FStar_Ident.lid_of_ns_and_id
                               tac_lid.FStar_Ident.ns uu____2727
                              in
                           let uu____2728 = is_tactic_decl assm_lid h1  in
                           if uu____2728
                           then
                             let uu____2731 =
                               let uu____2732 =
                                 let uu____2733 = FStar_List.hd args  in
                                 FStar_Pervasives_Native.fst uu____2733  in
                               mk_registration tac_lid assm_lid uu____2732 bs
                                in
                             [uu____2731]
                           else []
                       | uu____2749 -> []))
             | uu____2750 -> []  in
           let uu____2753 = FStar_Extraction_ML_Term.term_as_mlexpr g elet
              in
           (match uu____2753 with
            | (ml_let,uu____2767,uu____2768) ->
                (match ml_let.FStar_Extraction_ML_Syntax.expr with
                 | FStar_Extraction_ML_Syntax.MLE_Let
                     ((flavor,uu____2776,bindings),uu____2778) ->
                     let uu____2791 =
                       FStar_List.fold_left2
                         (fun uu____2818  ->
                            fun ml_lb  ->
                              fun uu____2820  ->
                                match (uu____2818, uu____2820) with
                                | ((env,ml_lbs),{
                                                  FStar_Syntax_Syntax.lbname
                                                    = lbname;
                                                  FStar_Syntax_Syntax.lbunivs
                                                    = uu____2842;
                                                  FStar_Syntax_Syntax.lbtyp =
                                                    t;
                                                  FStar_Syntax_Syntax.lbeff =
                                                    uu____2844;
                                                  FStar_Syntax_Syntax.lbdef =
                                                    uu____2845;_})
                                    ->
                                    let lb_lid =
                                      let uu____2867 =
                                        let uu____2870 =
                                          FStar_Util.right lbname  in
                                        uu____2870.FStar_Syntax_Syntax.fv_name
                                         in
                                      uu____2867.FStar_Syntax_Syntax.v  in
                                    let uu____2871 =
                                      let uu____2876 =
                                        FStar_All.pipe_right quals
                                          (FStar_Util.for_some
                                             (fun uu___157_2881  ->
                                                match uu___157_2881 with
                                                | FStar_Syntax_Syntax.Projector
                                                    uu____2882 -> true
                                                | uu____2887 -> false))
                                         in
                                      if uu____2876
                                      then
                                        let mname =
                                          let uu____2893 =
                                            mangle_projector_lid lb_lid  in
                                          FStar_All.pipe_right uu____2893
                                            FStar_Extraction_ML_Syntax.mlpath_of_lident
                                           in
                                        let uu____2894 =
                                          let uu____2899 =
                                            FStar_Util.right lbname  in
                                          let uu____2900 =
                                            FStar_Util.must
                                              ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc
                                             in
                                          FStar_Extraction_ML_UEnv.extend_fv'
                                            env uu____2899 mname uu____2900
                                            ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                            false
                                           in
                                        match uu____2894 with
                                        | (env1,uu____2906) ->
                                            (env1,
                                              (let uu___161_2908 = ml_lb  in
                                               {
                                                 FStar_Extraction_ML_Syntax.mllb_name
                                                   =
                                                   ((FStar_Pervasives_Native.snd
                                                       mname),
                                                     (Prims.parse_int "0"));
                                                 FStar_Extraction_ML_Syntax.mllb_tysc
                                                   =
                                                   (uu___161_2908.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                 FStar_Extraction_ML_Syntax.mllb_add_unit
                                                   =
                                                   (uu___161_2908.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                 FStar_Extraction_ML_Syntax.mllb_def
                                                   =
                                                   (uu___161_2908.FStar_Extraction_ML_Syntax.mllb_def);
                                                 FStar_Extraction_ML_Syntax.print_typ
                                                   =
                                                   (uu___161_2908.FStar_Extraction_ML_Syntax.print_typ)
                                               }))
                                      else
                                        (let uu____2912 =
                                           let uu____2913 =
                                             let uu____2918 =
                                               FStar_Util.must
                                                 ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc
                                                in
                                             FStar_Extraction_ML_UEnv.extend_lb
                                               env lbname t uu____2918
                                               ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                               false
                                              in
                                           FStar_All.pipe_left
                                             FStar_Pervasives_Native.fst
                                             uu____2913
                                            in
                                         (uu____2912, ml_lb))
                                       in
                                    (match uu____2871 with
                                     | (g1,ml_lb1) ->
                                         (g1, (ml_lb1 :: ml_lbs)))) (g, [])
                         bindings (FStar_Pervasives_Native.snd lbs)
                        in
                     (match uu____2791 with
                      | (g1,ml_lbs') ->
                          let flags =
                            FStar_List.choose
                              (fun uu___158_2953  ->
                                 match uu___158_2953 with
                                 | FStar_Syntax_Syntax.Assumption  ->
                                     FStar_Pervasives_Native.Some
                                       FStar_Extraction_ML_Syntax.Assumed
                                 | FStar_Syntax_Syntax.Private  ->
                                     FStar_Pervasives_Native.Some
                                       FStar_Extraction_ML_Syntax.Private
                                 | FStar_Syntax_Syntax.NoExtract  ->
                                     FStar_Pervasives_Native.Some
                                       FStar_Extraction_ML_Syntax.NoExtract
                                 | uu____2956 -> FStar_Pervasives_Native.None)
                              quals
                             in
                          let flags' = extract_metadata attrs  in
                          let uu____2960 =
                            let uu____2963 =
                              let uu____2966 =
                                let uu____2967 =
                                  FStar_Extraction_ML_Util.mlloc_of_range
                                    se.FStar_Syntax_Syntax.sigrng
                                   in
                                FStar_Extraction_ML_Syntax.MLM_Loc uu____2967
                                 in
                              [uu____2966;
                              FStar_Extraction_ML_Syntax.MLM_Let
                                (flavor, (FStar_List.append flags flags'),
                                  (FStar_List.rev ml_lbs'))]
                               in
                            FStar_List.append uu____2963
                              tactic_registration_decl
                             in
                          (g1, uu____2960))
                 | uu____2974 ->
                     let uu____2975 =
                       let uu____2976 =
                         FStar_Extraction_ML_Code.string_of_mlexpr
                           g.FStar_Extraction_ML_UEnv.currentModule ml_let
                          in
                       FStar_Util.format1
                         "Impossible: Translated a let to a non-let: %s"
                         uu____2976
                        in
                     failwith uu____2975))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____2984,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____2989 =
             FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption)
              in
           if uu____2989
           then
             let always_fail =
               let imp =
                 let uu____3000 = FStar_Syntax_Util.arrow_formals t  in
                 match uu____3000 with
                 | ([],t1) ->
                     let b =
                       let uu____3029 =
                         FStar_Syntax_Syntax.gen_bv "_"
                           FStar_Pervasives_Native.None t1
                          in
                       FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                         uu____3029
                        in
                     let uu____3030 = fail_exp lid t1  in
                     FStar_Syntax_Util.abs [b] uu____3030
                       FStar_Pervasives_Native.None
                 | (bs,t1) ->
                     let uu____3049 = fail_exp lid t1  in
                     FStar_Syntax_Util.abs bs uu____3049
                       FStar_Pervasives_Native.None
                  in
               let uu___162_3050 = se  in
               let uu____3051 =
                 let uu____3052 =
                   let uu____3059 =
                     let uu____3066 =
                       let uu____3069 =
                         let uu____3070 =
                           let uu____3075 =
                             FStar_Syntax_Syntax.lid_as_fv lid
                               FStar_Syntax_Syntax.Delta_constant
                               FStar_Pervasives_Native.None
                              in
                           FStar_Util.Inr uu____3075  in
                         {
                           FStar_Syntax_Syntax.lbname = uu____3070;
                           FStar_Syntax_Syntax.lbunivs = [];
                           FStar_Syntax_Syntax.lbtyp = t;
                           FStar_Syntax_Syntax.lbeff =
                             FStar_Parser_Const.effect_ML_lid;
                           FStar_Syntax_Syntax.lbdef = imp
                         }  in
                       [uu____3069]  in
                     (false, uu____3066)  in
                   (uu____3059, [])  in
                 FStar_Syntax_Syntax.Sig_let uu____3052  in
               {
                 FStar_Syntax_Syntax.sigel = uu____3051;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___162_3050.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___162_3050.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___162_3050.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___162_3050.FStar_Syntax_Syntax.sigattrs)
               }  in
             let uu____3086 = extract_sig g always_fail  in
             (match uu____3086 with
              | (g1,mlm) ->
                  let uu____3105 =
                    FStar_Util.find_map quals
                      (fun uu___159_3110  ->
                         match uu___159_3110 with
                         | FStar_Syntax_Syntax.Discriminator l ->
                             FStar_Pervasives_Native.Some l
                         | uu____3114 -> FStar_Pervasives_Native.None)
                     in
                  (match uu____3105 with
                   | FStar_Pervasives_Native.Some l ->
                       let uu____3122 =
                         let uu____3125 =
                           let uu____3126 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng
                              in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____3126  in
                         let uu____3127 =
                           let uu____3130 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l
                              in
                           [uu____3130]  in
                         uu____3125 :: uu____3127  in
                       (g1, uu____3122)
                   | uu____3133 ->
                       let uu____3136 =
                         FStar_Util.find_map quals
                           (fun uu___160_3142  ->
                              match uu___160_3142 with
                              | FStar_Syntax_Syntax.Projector (l,uu____3146)
                                  -> FStar_Pervasives_Native.Some l
                              | uu____3147 -> FStar_Pervasives_Native.None)
                          in
                       (match uu____3136 with
                        | FStar_Pervasives_Native.Some uu____3154 -> (g1, [])
                        | uu____3157 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____3166 = FStar_Extraction_ML_Term.term_as_mlexpr g e  in
           (match uu____3166 with
            | (ml_main,uu____3180,uu____3181) ->
                let uu____3182 =
                  let uu____3185 =
                    let uu____3186 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng
                       in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____3186  in
                  [uu____3185; FStar_Extraction_ML_Syntax.MLM_Top ml_main]
                   in
                (g, uu____3182))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____3189 ->
           failwith "impossible -- removed by tc.fs"
       | FStar_Syntax_Syntax.Sig_assume uu____3196 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____3205 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____3208 -> (g, [])
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (if p = FStar_Syntax_Syntax.LightOff
            then FStar_Options.set_ml_ish ()
            else ();
            (g, [])))
  
let extract_iface :
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.modul -> env_t =
  fun g  ->
    fun m  ->
      let uu____3236 =
        FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____3236 FStar_Pervasives_Native.fst
  
let extract :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Extraction_ML_UEnv.env,FStar_Extraction_ML_Syntax.mllib
                                      Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun g  ->
    fun m  ->
      FStar_Syntax_Syntax.reset_gensym ();
      (let uu____3281 = FStar_Options.debug_any ()  in
       if uu____3281
       then
         let uu____3282 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name  in
         FStar_Util.print1 "Extracting module %s\n" uu____3282
       else ());
      (let uu____3284 = FStar_Options.restore_cmd_line_options true  in
       let name =
         FStar_Extraction_ML_Syntax.mlpath_of_lident
           m.FStar_Syntax_Syntax.name
          in
       let g1 =
         let uu___163_3287 = g  in
         let uu____3288 =
           FStar_TypeChecker_Env.set_current_module
             g.FStar_Extraction_ML_UEnv.tcenv m.FStar_Syntax_Syntax.name
            in
         {
           FStar_Extraction_ML_UEnv.tcenv = uu____3288;
           FStar_Extraction_ML_UEnv.gamma =
             (uu___163_3287.FStar_Extraction_ML_UEnv.gamma);
           FStar_Extraction_ML_UEnv.tydefs =
             (uu___163_3287.FStar_Extraction_ML_UEnv.tydefs);
           FStar_Extraction_ML_UEnv.type_names =
             (uu___163_3287.FStar_Extraction_ML_UEnv.type_names);
           FStar_Extraction_ML_UEnv.currentModule = name
         }  in
       let uu____3289 =
         FStar_Util.fold_map extract_sig g1
           m.FStar_Syntax_Syntax.declarations
          in
       match uu____3289 with
       | (g2,sigs) ->
           let mlm = FStar_List.flatten sigs  in
           let is_kremlin =
             let uu____3318 = FStar_Options.codegen ()  in
             match uu____3318 with
             | FStar_Pervasives_Native.Some "Kremlin" -> true
             | uu____3321 -> false  in
           let uu____3324 =
             (((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
                (is_kremlin ||
                   (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)))
               &&
               (FStar_Options.should_extract
                  (m.FStar_Syntax_Syntax.name).FStar_Ident.str)
              in
           if uu____3324
           then
             ((let uu____3332 =
                 FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name
                  in
               FStar_Util.print1 "Extracted module %s\n" uu____3332);
              (g2,
                [FStar_Extraction_ML_Syntax.MLLib
                   [(name, (FStar_Pervasives_Native.Some ([], mlm)),
                      (FStar_Extraction_ML_Syntax.MLLib []))]]))
           else (g2, []))
  