open Prims
let fail_exp lid t =
  let uu____18 =
    let uu____21 =
      let uu____22 =
        let uu____32 =
          FStar_Syntax_Syntax.fvar FStar_Parser_Const.failwith_lid
            FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
           in
        let uu____33 =
          let uu____35 = FStar_Syntax_Syntax.iarg t  in
          let uu____36 =
            let uu____38 =
              let uu____39 =
                let uu____40 =
                  let uu____43 =
                    let uu____44 =
                      let uu____45 =
                        let uu____49 =
                          let uu____50 =
                            let uu____51 =
                              FStar_Syntax_Print.lid_to_string lid  in
                            Prims.strcat "Not yet implemented:" uu____51  in
                          FStar_Bytes.string_as_unicode_bytes uu____50  in
                        (uu____49, FStar_Range.dummyRange)  in
                      FStar_Const.Const_string uu____45  in
                    FStar_Syntax_Syntax.Tm_constant uu____44  in
                  FStar_Syntax_Syntax.mk uu____43  in
                uu____40 FStar_Pervasives_Native.None FStar_Range.dummyRange
                 in
              FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____39  in
            [uu____38]  in
          uu____35 :: uu____36  in
        (uu____32, uu____33)  in
      FStar_Syntax_Syntax.Tm_app uu____22  in
    FStar_Syntax_Syntax.mk uu____21  in
  uu____18 FStar_Pervasives_Native.None FStar_Range.dummyRange 
let mangle_projector_lid : FStar_Ident.lident -> FStar_Ident.lident =
  fun x  -> x 
let lident_as_mlsymbol : FStar_Ident.lident -> Prims.string =
  fun id  -> (id.FStar_Ident.ident).FStar_Ident.idText 
let as_pair uu___147_88 =
  match uu___147_88 with
  | a::b::[] -> (a, b)
  | uu____92 -> failwith "Expected a list with 2 elements" 
let rec extract_attr :
  FStar_Syntax_Syntax.term ->
    FStar_Extraction_ML_Syntax.tyattr FStar_Pervasives_Native.option
  =
  fun x  ->
    let uu____101 = FStar_Syntax_Subst.compress x  in
    match uu____101 with
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
        FStar_Syntax_Syntax.tk = uu____104;
        FStar_Syntax_Syntax.pos = uu____105;
        FStar_Syntax_Syntax.vars = uu____106;_} when
        let uu____109 =
          let uu____110 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____110  in
        uu____109 = "FStar.Pervasives.PpxDeriving" ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.PpxDeriving
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.tk = uu____112;
             FStar_Syntax_Syntax.pos = uu____113;
             FStar_Syntax_Syntax.vars = uu____114;_},({
                                                        FStar_Syntax_Syntax.n
                                                          =
                                                          FStar_Syntax_Syntax.Tm_constant
                                                          (FStar_Const.Const_string
                                                          (data,uu____116));
                                                        FStar_Syntax_Syntax.tk
                                                          = uu____117;
                                                        FStar_Syntax_Syntax.pos
                                                          = uu____118;
                                                        FStar_Syntax_Syntax.vars
                                                          = uu____119;_},uu____120)::[]);
        FStar_Syntax_Syntax.tk = uu____121;
        FStar_Syntax_Syntax.pos = uu____122;
        FStar_Syntax_Syntax.vars = uu____123;_} when
        let uu____149 =
          let uu____150 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____150  in
        uu____149 = "FStar.Pervasives.PpxDerivingConstant" ->
        FStar_Pervasives_Native.Some
          (FStar_Extraction_ML_Syntax.PpxDerivingConstant
             (FStar_Util.string_of_unicode data))
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_meta (x1,uu____152);
        FStar_Syntax_Syntax.tk = uu____153;
        FStar_Syntax_Syntax.pos = uu____154;
        FStar_Syntax_Syntax.vars = uu____155;_} -> extract_attr x1
    | a -> FStar_Pervasives_Native.None
  
let extract_attrs :
  FStar_Syntax_Syntax.term Prims.list ->
    FStar_Extraction_ML_Syntax.tyattr Prims.list
  = fun attrs  -> FStar_List.choose extract_attr attrs 
let binders_as_mlty_binders env bs =
  FStar_Util.fold_map
    (fun env1  ->
       fun uu____207  ->
         match uu____207 with
         | (bv,uu____215) ->
             let uu____216 =
               let uu____217 =
                 let uu____219 =
                   let uu____220 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv
                      in
                   FStar_Extraction_ML_Syntax.MLTY_Var uu____220  in
                 FStar_Pervasives_Native.Some uu____219  in
               FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____217  in
             let uu____221 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv  in
             (uu____216, uu____221)) env bs
  
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
              let uu____255 =
                let uu____256 = FStar_Syntax_Subst.compress def  in
                FStar_All.pipe_right uu____256 FStar_Syntax_Util.unmeta  in
              FStar_All.pipe_right uu____255 FStar_Syntax_Util.un_uinst  in
            let def2 =
              match def1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_abs uu____258 ->
                  FStar_Extraction_ML_Term.normalize_abs def1
              | uu____268 -> def1  in
            let uu____269 =
              match def2.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____276) ->
                  FStar_Syntax_Subst.open_term bs body
              | uu____289 -> ([], def2)  in
            match uu____269 with
            | (bs,body) ->
                let assumed =
                  FStar_Util.for_some
                    (fun uu___148_302  ->
                       match uu___148_302 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____303 -> false) quals
                   in
                let uu____304 = binders_as_mlty_binders env bs  in
                (match uu____304 with
                 | (env1,ml_bs) ->
                     let body1 =
                       let uu____322 =
                         FStar_Extraction_ML_Term.term_as_mlty env1 body  in
                       FStar_All.pipe_right uu____322
                         (FStar_Extraction_ML_Util.eraseTypeDeep
                            (FStar_Extraction_ML_Util.udelta_unfold env1))
                        in
                     let mangled_projector =
                       let uu____325 =
                         FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___149_329  ->
                                 match uu___149_329 with
                                 | FStar_Syntax_Syntax.Projector uu____330 ->
                                     true
                                 | uu____333 -> false))
                          in
                       if uu____325
                       then
                         let mname = mangle_projector_lid lid  in
                         FStar_Pervasives_Native.Some
                           ((mname.FStar_Ident.ident).FStar_Ident.idText)
                       else FStar_Pervasives_Native.None  in
                     let attrs1 = extract_attrs attrs  in
                     let td =
                       let uu____353 =
                         let uu____366 = lident_as_mlsymbol lid  in
                         (assumed, uu____366, mangled_projector, ml_bs,
                           attrs1,
                           (FStar_Pervasives_Native.Some
                              (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1)))
                          in
                       [uu____353]  in
                     let def3 =
                       let uu____399 =
                         let uu____400 =
                           FStar_Extraction_ML_Util.mlloc_of_range
                             (FStar_Ident.range_of_lid lid)
                            in
                         FStar_Extraction_ML_Syntax.MLM_Loc uu____400  in
                       [uu____399; FStar_Extraction_ML_Syntax.MLM_Ty td]  in
                     let env2 =
                       let uu____402 =
                         FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___150_405  ->
                                 match uu___150_405 with
                                 | FStar_Syntax_Syntax.Assumption  -> true
                                 | FStar_Syntax_Syntax.New  -> true
                                 | uu____406 -> false))
                          in
                       if uu____402
                       then env1
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
  iattrs: FStar_Extraction_ML_Syntax.tyattrs }
let __proj__Mkinductive_family__item__iname :
  inductive_family -> FStar_Ident.lident =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; iattrs = __fname__iattrs;_} ->
        __fname__iname
  
let __proj__Mkinductive_family__item__iparams :
  inductive_family -> FStar_Syntax_Syntax.binders =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; iattrs = __fname__iattrs;_} ->
        __fname__iparams
  
let __proj__Mkinductive_family__item__ityp :
  inductive_family -> FStar_Syntax_Syntax.term =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; iattrs = __fname__iattrs;_} ->
        __fname__ityp
  
let __proj__Mkinductive_family__item__idatas :
  inductive_family -> data_constructor Prims.list =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; iattrs = __fname__iattrs;_} ->
        __fname__idatas
  
let __proj__Mkinductive_family__item__iquals :
  inductive_family -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; iattrs = __fname__iattrs;_} ->
        __fname__iquals
  
let __proj__Mkinductive_family__item__iattrs :
  inductive_family -> FStar_Extraction_ML_Syntax.tyattrs =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; iattrs = __fname__iattrs;_} ->
        __fname__iattrs
  
let print_ifamily : inductive_family -> Prims.unit =
  fun i  ->
    let uu____535 = FStar_Syntax_Print.lid_to_string i.iname  in
    let uu____536 = FStar_Syntax_Print.binders_to_string " " i.iparams  in
    let uu____537 = FStar_Syntax_Print.term_to_string i.ityp  in
    let uu____538 =
      let uu____539 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let uu____547 = FStar_Syntax_Print.lid_to_string d.dname  in
                let uu____548 =
                  let uu____549 = FStar_Syntax_Print.term_to_string d.dtyp
                     in
                  Prims.strcat " : " uu____549  in
                Prims.strcat uu____547 uu____548))
         in
      FStar_All.pipe_right uu____539 (FStar_String.concat "\n\t\t")  in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____535 uu____536 uu____537
      uu____538
  
let bundle_as_inductive_families env ses quals attrs =
  FStar_All.pipe_right ses
    (FStar_List.collect
       (fun se  ->
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_inductive_typ (l,_us,bs,t,_mut_i,datas)
              ->
              let uu____612 = FStar_Syntax_Subst.open_term bs t  in
              (match uu____612 with
               | (bs1,t1) ->
                   let datas1 =
                     FStar_All.pipe_right ses
                       (FStar_List.collect
                          (fun se1  ->
                             match se1.FStar_Syntax_Syntax.sigel with
                             | FStar_Syntax_Syntax.Sig_datacon
                                 (d,uu____640,t2,l',nparams,uu____644) when
                                 FStar_Ident.lid_equals l l' ->
                                 let uu____647 =
                                   FStar_Syntax_Util.arrow_formals t2  in
                                 (match uu____647 with
                                  | (bs',body) ->
                                      let uu____668 =
                                        FStar_Util.first_N
                                          (FStar_List.length bs1) bs'
                                         in
                                      (match uu____668 with
                                       | (bs_params,rest) ->
                                           let subst1 =
                                             FStar_List.map2
                                               (fun uu____713  ->
                                                  fun uu____714  ->
                                                    match (uu____713,
                                                            uu____714)
                                                    with
                                                    | ((b',uu____724),
                                                       (b,uu____726)) ->
                                                        let uu____731 =
                                                          let uu____736 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              b
                                                             in
                                                          (b', uu____736)  in
                                                        FStar_Syntax_Syntax.NT
                                                          uu____731)
                                               bs_params bs1
                                              in
                                           let t3 =
                                             let uu____738 =
                                               let uu____741 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   body
                                                  in
                                               FStar_Syntax_Util.arrow rest
                                                 uu____741
                                                in
                                             FStar_All.pipe_right uu____738
                                               (FStar_Syntax_Subst.subst
                                                  subst1)
                                              in
                                           [{ dname = d; dtyp = t3 }]))
                             | uu____746 -> []))
                      in
                   let attrs1 =
                     extract_attrs
                       (FStar_List.append se.FStar_Syntax_Syntax.sigattrs
                          attrs)
                      in
                   [{
                      iname = l;
                      iparams = bs1;
                      ityp = t1;
                      idatas = datas1;
                      iquals = (se.FStar_Syntax_Syntax.sigquals);
                      iattrs = attrs1
                    }])
          | uu____749 -> []))
  
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
          let uu____792 =
            FStar_Extraction_ML_Term.term_as_mlty env1 ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env1) uu____792
           in
        let steps =
          [FStar_TypeChecker_Normalize.Inlining;
          FStar_TypeChecker_Normalize.UnfoldUntil
            FStar_Syntax_Syntax.Delta_constant;
          FStar_TypeChecker_Normalize.EraseUniverses;
          FStar_TypeChecker_Normalize.AllowUnboundUniverses]  in
        let names1 =
          let uu____797 =
            let uu____798 =
              let uu____801 =
                FStar_TypeChecker_Normalize.normalize steps
                  env1.FStar_Extraction_ML_UEnv.tcenv ctor.dtyp
                 in
              FStar_Syntax_Subst.compress uu____801  in
            uu____798.FStar_Syntax_Syntax.n  in
          match uu____797 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,uu____804) ->
              FStar_List.map
                (fun uu____822  ->
                   match uu____822 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____826;
                        FStar_Syntax_Syntax.sort = uu____827;_},uu____828)
                       -> ppname.FStar_Ident.idText) bs
          | uu____831 -> []  in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____842 =
          let uu____843 =
            FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
          FStar_Pervasives_Native.fst uu____843  in
        let uu____846 =
          let uu____852 = lident_as_mlsymbol ctor.dname  in
          let uu____853 =
            let uu____857 = FStar_Extraction_ML_Util.argTypes mlt  in
            FStar_List.zip names1 uu____857  in
          (uu____852, uu____853)  in
        (uu____842, uu____846)  in
      let extract_one_family env1 ind =
        let uu____887 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____887 with
        | (env2,vars) ->
            let uu____914 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor vars) env2)
               in
            (match uu____914 with
             | (env3,ctors) ->
                 let uu____964 = FStar_Syntax_Util.arrow_formals ind.ityp  in
                 (match uu____964 with
                  | (indices,uu____986) ->
                      let ml_params =
                        let uu____1001 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____1019  ->
                                    let uu____1022 =
                                      let uu____1023 =
                                        FStar_Util.string_of_int i  in
                                      Prims.strcat "'dummyV" uu____1023  in
                                    (uu____1022, (Prims.parse_int "0"))))
                           in
                        FStar_List.append vars uu____1001  in
                      let tbody =
                        let uu____1027 =
                          FStar_Util.find_opt
                            (fun uu___151_1031  ->
                               match uu___151_1031 with
                               | FStar_Syntax_Syntax.RecordType uu____1032 ->
                                   true
                               | uu____1037 -> false) ind.iquals
                           in
                        match uu____1027 with
                        | FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____1044 = FStar_List.hd ctors  in
                            (match uu____1044 with
                             | (uu____1055,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id  ->
                                        fun uu____1080  ->
                                          match uu____1080 with
                                          | (uu____1085,ty) ->
                                              let lid =
                                                FStar_Ident.lid_of_ids
                                                  (FStar_List.append ns [id])
                                                 in
                                              let uu____1088 =
                                                lident_as_mlsymbol lid  in
                                              (uu____1088, ty)) ids c_ty
                                    in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____1089 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors
                         in
                      let uu____1091 =
                        let uu____1103 = lident_as_mlsymbol ind.iname  in
                        (false, uu____1103, FStar_Pervasives_Native.None,
                          ml_params, (ind.iattrs),
                          (FStar_Pervasives_Native.Some tbody))
                         in
                      (env3, uu____1091)))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____1125,t,uu____1127,uu____1128,uu____1129);
            FStar_Syntax_Syntax.sigrng = uu____1130;
            FStar_Syntax_Syntax.sigquals = uu____1131;
            FStar_Syntax_Syntax.sigmeta = uu____1132;
            FStar_Syntax_Syntax.sigattrs = uu____1133;_}::[],uu____1134),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____1143 = extract_ctor [] env { dname = l; dtyp = t }  in
          (match uu____1143 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____1170),quals) ->
          let ifams =
            bundle_as_inductive_families env ses quals
              se.FStar_Syntax_Syntax.sigattrs
             in
          let uu____1181 = FStar_Util.fold_map extract_one_family env ifams
             in
          (match uu____1181 with
           | (env1,td) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Ty td]))
      | uu____1237 -> failwith "Unexpected signature element"
  
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
           let uu____1262 = FStar_Syntax_Print.sigelt_to_string se  in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____1262);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____1266 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____1271 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____1280 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
           ->
           let extend_env g1 lid ml_name tm tysc =
             let uu____1308 =
               let uu____1311 =
                 FStar_Syntax_Syntax.lid_as_fv lid
                   FStar_Syntax_Syntax.Delta_equational
                   FStar_Pervasives_Native.None
                  in
               FStar_Extraction_ML_UEnv.extend_fv' g1 uu____1311 ml_name tysc
                 false false
                in
             match uu____1308 with
             | (g2,mangled_name) ->
                 ((let uu____1317 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          g2.FStar_Extraction_ML_UEnv.tcenv)
                       (FStar_Options.Other "ExtractionReify")
                      in
                   if uu____1317
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
             (let uu____1329 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify")
                 in
              if uu____1329
              then
                let uu____1330 = FStar_Syntax_Print.term_to_string tm  in
                FStar_Util.print1 "extract_fv term: %s\n" uu____1330
              else ());
             (let uu____1332 =
                let uu____1333 = FStar_Syntax_Subst.compress tm  in
                uu____1333.FStar_Syntax_Syntax.n  in
              match uu____1332 with
              | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____1339) ->
                  extract_fv tm1
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let mlp =
                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                     in
                  let uu____1346 =
                    let uu____1351 = FStar_Extraction_ML_UEnv.lookup_fv g fv
                       in
                    FStar_All.pipe_left FStar_Util.right uu____1351  in
                  (match uu____1346 with
                   | (uu____1380,uu____1381,tysc,uu____1383) ->
                       let uu____1384 =
                         FStar_All.pipe_left
                           (FStar_Extraction_ML_Syntax.with_ty
                              FStar_Extraction_ML_Syntax.MLTY_Top)
                           (FStar_Extraction_ML_Syntax.MLE_Name mlp)
                          in
                       (uu____1384, tysc))
              | uu____1385 -> failwith "Not an fv")
              in
           let extract_action g1 a =
             (let uu____1407 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g1.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify")
                 in
              if uu____1407
              then
                let uu____1408 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_typ
                   in
                let uu____1409 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_defn
                   in
                FStar_Util.print2 "Action type %s and term %s\n" uu____1408
                  uu____1409
              else ());
             (let uu____1411 = FStar_Extraction_ML_UEnv.action_name ed a  in
              match uu____1411 with
              | (a_nm,a_lid) ->
                  let lbname =
                    let uu____1421 =
                      FStar_Syntax_Syntax.new_bv
                        (FStar_Pervasives_Native.Some
                           ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                        FStar_Syntax_Syntax.tun
                       in
                    FStar_Util.Inl uu____1421  in
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
                  let uu____1442 =
                    FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb  in
                  (match uu____1442 with
                   | (a_let,uu____1449,ty) ->
                       ((let uu____1452 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug
                                g1.FStar_Extraction_ML_UEnv.tcenv)
                             (FStar_Options.Other "ExtractionReify")
                            in
                         if uu____1452
                         then
                           let uu____1453 =
                             FStar_Extraction_ML_Code.string_of_mlexpr a_nm
                               a_let
                              in
                           FStar_Util.print1 "Extracted action term: %s\n"
                             uu____1453
                         else ());
                        (let uu____1455 =
                           match a_let.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_Let
                               ((uu____1460,uu____1461,mllb::[]),uu____1463)
                               ->
                               (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                                with
                                | FStar_Pervasives_Native.Some tysc ->
                                    ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                      tysc)
                                | FStar_Pervasives_Native.None  ->
                                    failwith "No type scheme")
                           | uu____1474 -> failwith "Impossible"  in
                         match uu____1455 with
                         | (exp,tysc) ->
                             ((let uu____1482 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug
                                      g1.FStar_Extraction_ML_UEnv.tcenv)
                                   (FStar_Options.Other "ExtractionReify")
                                  in
                               if uu____1482
                               then
                                 ((let uu____1484 =
                                     FStar_Extraction_ML_Code.string_of_mlty
                                       a_nm
                                       (FStar_Pervasives_Native.snd tysc)
                                      in
                                   FStar_Util.print1
                                     "Extracted action type: %s\n" uu____1484);
                                  FStar_List.iter
                                    (fun x  ->
                                       FStar_Util.print1 "and binders: %s\n"
                                         (FStar_Pervasives_Native.fst x))
                                    (FStar_Pervasives_Native.fst tysc))
                               else ());
                              extend_env g1 a_lid a_nm exp tysc)))))
              in
           let uu____1492 =
             let uu____1495 =
               extract_fv
                 (FStar_Pervasives_Native.snd
                    ed.FStar_Syntax_Syntax.return_repr)
                in
             match uu____1495 with
             | (return_tm,ty_sc) ->
                 let uu____1503 =
                   FStar_Extraction_ML_UEnv.monad_op_name ed "return"  in
                 (match uu____1503 with
                  | (return_nm,return_lid) ->
                      extend_env g return_lid return_nm return_tm ty_sc)
              in
           (match uu____1492 with
            | (g1,return_decl) ->
                let uu____1515 =
                  let uu____1518 =
                    extract_fv
                      (FStar_Pervasives_Native.snd
                         ed.FStar_Syntax_Syntax.bind_repr)
                     in
                  match uu____1518 with
                  | (bind_tm,ty_sc) ->
                      let uu____1526 =
                        FStar_Extraction_ML_UEnv.monad_op_name ed "bind"  in
                      (match uu____1526 with
                       | (bind_nm,bind_lid) ->
                           extend_env g1 bind_lid bind_nm bind_tm ty_sc)
                   in
                (match uu____1515 with
                 | (g2,bind_decl) ->
                     let uu____1538 =
                       FStar_Util.fold_map extract_action g2
                         ed.FStar_Syntax_Syntax.actions
                        in
                     (match uu____1538 with
                      | (g3,actions) ->
                          (g3,
                            (FStar_List.append [return_decl; bind_decl]
                               actions)))))
       | FStar_Syntax_Syntax.Sig_new_effect uu____1550 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____1553,t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let uu____1559 =
             let uu____1560 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___152_1563  ->
                       match uu___152_1563 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____1564 -> false))
                in
             Prims.op_Negation uu____1560  in
           if uu____1559
           then (g, [])
           else
             (let uu____1570 = FStar_Syntax_Util.arrow_formals t  in
              match uu____1570 with
              | (bs,uu____1582) ->
                  let fv =
                    FStar_Syntax_Syntax.lid_as_fv lid
                      FStar_Syntax_Syntax.Delta_constant
                      FStar_Pervasives_Native.None
                     in
                  let uu____1594 =
                    FStar_Syntax_Util.abs bs FStar_TypeChecker_Common.t_unit
                      FStar_Pervasives_Native.None
                     in
                  extract_typ_abbrev g fv quals attrs uu____1594)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____1596) when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____1605 =
             let uu____1610 =
               FStar_TypeChecker_Env.open_universes_in
                 g.FStar_Extraction_ML_UEnv.tcenv
                 lb.FStar_Syntax_Syntax.lbunivs
                 [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp]
                in
             match uu____1610 with
             | (tcenv,uu____1626,def_typ) ->
                 let uu____1630 = as_pair def_typ  in (tcenv, uu____1630)
              in
           (match uu____1605 with
            | (tcenv,(lbdef,lbtyp)) ->
                let lbtyp1 =
                  FStar_TypeChecker_Normalize.unfold_whnf tcenv lbtyp  in
                let lbdef1 =
                  FStar_TypeChecker_Normalize.eta_expand_with_type tcenv
                    lbdef lbtyp1
                   in
                let uu____1645 =
                  FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                extract_typ_abbrev g uu____1645 quals
                  se.FStar_Syntax_Syntax.sigattrs lbdef1)
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____1647) ->
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
               | FStar_Syntax_Syntax.Tm_uinst (h',uu____1673) ->
                   let uu____1678 =
                     let uu____1679 = FStar_Syntax_Subst.compress h'  in
                     uu____1679.FStar_Syntax_Syntax.n  in
                   (match uu____1678 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.tactic_lid
                        ->
                        let uu____1683 =
                          let uu____1684 =
                            FStar_Extraction_ML_Syntax.string_of_mlpath
                              g.FStar_Extraction_ML_UEnv.currentModule
                             in
                          FStar_Util.starts_with uu____1684 "FStar.Tactics"
                           in
                        Prims.op_Negation uu____1683
                    | uu____1685 -> false)
               | uu____1686 -> false  in
             let mk_registration tac_lid assm_lid t bs =
               let h =
                 let uu____1707 =
                   let uu____1708 =
                     let uu____1709 =
                       FStar_Ident.lid_of_str
                         "FStar_Tactics_Native.register_tactic"
                        in
                     FStar_Extraction_ML_Syntax.mlpath_of_lident uu____1709
                      in
                   FStar_Extraction_ML_Syntax.MLE_Name uu____1708  in
                 FStar_All.pipe_left
                   (FStar_Extraction_ML_Syntax.with_ty
                      FStar_Extraction_ML_Syntax.MLTY_Top) uu____1707
                  in
               let lid_arg =
                 let uu____1711 =
                   let uu____1712 = FStar_Ident.string_of_lid assm_lid  in
                   FStar_Extraction_ML_Syntax.MLC_String uu____1712  in
                 FStar_Extraction_ML_Syntax.MLE_Const uu____1711  in
               let tac_arity = FStar_List.length bs  in
               let arity =
                 let uu____1719 =
                   let uu____1720 =
                     let uu____1721 =
                       FStar_Util.string_of_int
                         (tac_arity + (Prims.parse_int "1"))
                        in
                     FStar_Ident.lid_of_str uu____1721  in
                   FStar_Extraction_ML_Syntax.mlpath_of_lident uu____1720  in
                 FStar_Extraction_ML_Syntax.MLE_Name uu____1719  in
               let tac_interpretation =
                 FStar_Extraction_ML_Util.mk_interpretation_fun tac_lid
                   lid_arg t bs
                  in
               let app =
                 let uu____1730 =
                   let uu____1731 =
                     let uu____1735 =
                       FStar_List.map
                         (FStar_Extraction_ML_Syntax.with_ty
                            FStar_Extraction_ML_Syntax.MLTY_Top)
                         [lid_arg; arity; tac_interpretation]
                        in
                     (h, uu____1735)  in
                   FStar_Extraction_ML_Syntax.MLE_App uu____1731  in
                 FStar_All.pipe_left
                   (FStar_Extraction_ML_Syntax.with_ty
                      FStar_Extraction_ML_Syntax.MLTY_Top) uu____1730
                  in
               FStar_Extraction_ML_Syntax.MLM_Top app  in
             match FStar_Pervasives_Native.snd lbs with
             | hd1::[] ->
                 let uu____1741 =
                   FStar_Syntax_Util.arrow_formals_comp
                     hd1.FStar_Syntax_Syntax.lbtyp
                    in
                 (match uu____1741 with
                  | (bs,comp) ->
                      let t = FStar_Syntax_Util.comp_result comp  in
                      let uu____1759 =
                        let uu____1760 = FStar_Syntax_Subst.compress t  in
                        uu____1760.FStar_Syntax_Syntax.n  in
                      (match uu____1759 with
                       | FStar_Syntax_Syntax.Tm_app (h,args) ->
                           let h1 = FStar_Syntax_Subst.compress h  in
                           let tac_lid =
                             let uu____1782 =
                               let uu____1784 =
                                 FStar_Util.right
                                   hd1.FStar_Syntax_Syntax.lbname
                                  in
                               uu____1784.FStar_Syntax_Syntax.fv_name  in
                             uu____1782.FStar_Syntax_Syntax.v  in
                           let assm_lid =
                             let uu____1786 =
                               FStar_All.pipe_left FStar_Ident.id_of_text
                                 (Prims.strcat "__"
                                    (tac_lid.FStar_Ident.ident).FStar_Ident.idText)
                                in
                             FStar_Ident.lid_of_ns_and_id
                               tac_lid.FStar_Ident.ns uu____1786
                              in
                           let uu____1787 = is_tactic_decl assm_lid h1  in
                           if uu____1787
                           then
                             let uu____1789 =
                               let uu____1790 =
                                 let uu____1791 = FStar_List.hd args  in
                                 FStar_Pervasives_Native.fst uu____1791  in
                               mk_registration tac_lid assm_lid uu____1790 bs
                                in
                             [uu____1789]
                           else []
                       | uu____1803 -> []))
             | uu____1804 -> []  in
           let uu____1806 = FStar_Extraction_ML_Term.term_as_mlexpr g elet
              in
           (match uu____1806 with
            | (ml_let,uu____1814,uu____1815) ->
                (match ml_let.FStar_Extraction_ML_Syntax.expr with
                 | FStar_Extraction_ML_Syntax.MLE_Let
                     ((flavor,uu____1820,bindings),uu____1822) ->
                     let uu____1829 =
                       FStar_List.fold_left2
                         (fun uu____1850  ->
                            fun ml_lb  ->
                              fun uu____1852  ->
                                match (uu____1850, uu____1852) with
                                | ((env,ml_lbs),{
                                                  FStar_Syntax_Syntax.lbname
                                                    = lbname;
                                                  FStar_Syntax_Syntax.lbunivs
                                                    = uu____1865;
                                                  FStar_Syntax_Syntax.lbtyp =
                                                    t;
                                                  FStar_Syntax_Syntax.lbeff =
                                                    uu____1867;
                                                  FStar_Syntax_Syntax.lbdef =
                                                    uu____1868;_})
                                    ->
                                    let lb_lid =
                                      let uu____1882 =
                                        let uu____1884 =
                                          FStar_Util.right lbname  in
                                        uu____1884.FStar_Syntax_Syntax.fv_name
                                         in
                                      uu____1882.FStar_Syntax_Syntax.v  in
                                    let uu____1885 =
                                      let uu____1888 =
                                        FStar_All.pipe_right quals
                                          (FStar_Util.for_some
                                             (fun uu___153_1892  ->
                                                match uu___153_1892 with
                                                | FStar_Syntax_Syntax.Projector
                                                    uu____1893 -> true
                                                | uu____1896 -> false))
                                         in
                                      if uu____1888
                                      then
                                        let mname =
                                          let uu____1900 =
                                            mangle_projector_lid lb_lid  in
                                          FStar_All.pipe_right uu____1900
                                            FStar_Extraction_ML_Syntax.mlpath_of_lident
                                           in
                                        let uu____1901 =
                                          let uu____1904 =
                                            FStar_Util.right lbname  in
                                          let uu____1905 =
                                            FStar_Util.must
                                              ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc
                                             in
                                          FStar_Extraction_ML_UEnv.extend_fv'
                                            env uu____1904 mname uu____1905
                                            ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                            false
                                           in
                                        match uu____1901 with
                                        | (env1,uu____1909) ->
                                            (env1,
                                              (let uu___158_1911 = ml_lb  in
                                               {
                                                 FStar_Extraction_ML_Syntax.mllb_name
                                                   =
                                                   ((FStar_Pervasives_Native.snd
                                                       mname),
                                                     (Prims.parse_int "0"));
                                                 FStar_Extraction_ML_Syntax.mllb_tysc
                                                   =
                                                   (uu___158_1911.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                 FStar_Extraction_ML_Syntax.mllb_add_unit
                                                   =
                                                   (uu___158_1911.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                 FStar_Extraction_ML_Syntax.mllb_def
                                                   =
                                                   (uu___158_1911.FStar_Extraction_ML_Syntax.mllb_def);
                                                 FStar_Extraction_ML_Syntax.print_typ
                                                   =
                                                   (uu___158_1911.FStar_Extraction_ML_Syntax.print_typ)
                                               }))
                                      else
                                        (let uu____1914 =
                                           let uu____1915 =
                                             let uu____1918 =
                                               FStar_Util.must
                                                 ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc
                                                in
                                             FStar_Extraction_ML_UEnv.extend_lb
                                               env lbname t uu____1918
                                               ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                               false
                                              in
                                           FStar_All.pipe_left
                                             FStar_Pervasives_Native.fst
                                             uu____1915
                                            in
                                         (uu____1914, ml_lb))
                                       in
                                    (match uu____1885 with
                                     | (g1,ml_lb1) ->
                                         (g1, (ml_lb1 :: ml_lbs)))) (g, [])
                         bindings (FStar_Pervasives_Native.snd lbs)
                        in
                     (match uu____1829 with
                      | (g1,ml_lbs') ->
                          let flags =
                            FStar_List.choose
                              (fun uu___154_1939  ->
                                 match uu___154_1939 with
                                 | FStar_Syntax_Syntax.Assumption  ->
                                     FStar_Pervasives_Native.Some
                                       FStar_Extraction_ML_Syntax.Assumed
                                 | FStar_Syntax_Syntax.Private  ->
                                     FStar_Pervasives_Native.Some
                                       FStar_Extraction_ML_Syntax.Private
                                 | FStar_Syntax_Syntax.NoExtract  ->
                                     FStar_Pervasives_Native.Some
                                       FStar_Extraction_ML_Syntax.NoExtract
                                 | uu____1941 -> FStar_Pervasives_Native.None)
                              quals
                             in
                          let flags' =
                            FStar_List.choose
                              (fun uu___155_1952  ->
                                 match uu___155_1952 with
                                 | {
                                     FStar_Syntax_Syntax.n =
                                       FStar_Syntax_Syntax.Tm_constant
                                       (FStar_Const.Const_string
                                       (data,uu____1957));
                                     FStar_Syntax_Syntax.tk = uu____1958;
                                     FStar_Syntax_Syntax.pos = uu____1959;
                                     FStar_Syntax_Syntax.vars = uu____1960;_}
                                     ->
                                     FStar_Pervasives_Native.Some
                                       (FStar_Extraction_ML_Syntax.Attribute
                                          (FStar_Util.string_of_unicode data))
                                 | uu____1965 ->
                                     (FStar_Util.print_warning
                                        "Warning: unrecognized, non-string attribute, bother protz for a better error message";
                                      FStar_Pervasives_Native.None)) attrs
                             in
                          let uu____1969 =
                            let uu____1971 =
                              let uu____1973 =
                                let uu____1974 =
                                  FStar_Extraction_ML_Util.mlloc_of_range
                                    se.FStar_Syntax_Syntax.sigrng
                                   in
                                FStar_Extraction_ML_Syntax.MLM_Loc uu____1974
                                 in
                              [uu____1973;
                              FStar_Extraction_ML_Syntax.MLM_Let
                                (flavor, (FStar_List.append flags flags'),
                                  (FStar_List.rev ml_lbs'))]
                               in
                            FStar_List.append uu____1971
                              tactic_registration_decl
                             in
                          (g1, uu____1969))
                 | uu____1978 ->
                     let uu____1979 =
                       let uu____1980 =
                         FStar_Extraction_ML_Code.string_of_mlexpr
                           g.FStar_Extraction_ML_UEnv.currentModule ml_let
                          in
                       FStar_Util.format1
                         "Impossible: Translated a let to a non-let: %s"
                         uu____1980
                        in
                     failwith uu____1979))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____1985,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____1989 =
             FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption)
              in
           if uu____1989
           then
             let always_fail =
               let imp =
                 let uu____1996 = FStar_Syntax_Util.arrow_formals t  in
                 match uu____1996 with
                 | ([],t1) ->
                     let b =
                       let uu____2015 =
                         FStar_Syntax_Syntax.gen_bv "_"
                           FStar_Pervasives_Native.None t1
                          in
                       FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                         uu____2015
                        in
                     let uu____2016 = fail_exp lid t1  in
                     FStar_Syntax_Util.abs [b] uu____2016
                       FStar_Pervasives_Native.None
                 | (bs,t1) ->
                     let uu____2029 = fail_exp lid t1  in
                     FStar_Syntax_Util.abs bs uu____2029
                       FStar_Pervasives_Native.None
                  in
               let uu___159_2030 = se  in
               let uu____2031 =
                 let uu____2032 =
                   let uu____2036 =
                     let uu____2040 =
                       let uu____2042 =
                         let uu____2043 =
                           let uu____2046 =
                             FStar_Syntax_Syntax.lid_as_fv lid
                               FStar_Syntax_Syntax.Delta_constant
                               FStar_Pervasives_Native.None
                              in
                           FStar_Util.Inr uu____2046  in
                         {
                           FStar_Syntax_Syntax.lbname = uu____2043;
                           FStar_Syntax_Syntax.lbunivs = [];
                           FStar_Syntax_Syntax.lbtyp = t;
                           FStar_Syntax_Syntax.lbeff =
                             FStar_Parser_Const.effect_ML_lid;
                           FStar_Syntax_Syntax.lbdef = imp
                         }  in
                       [uu____2042]  in
                     (false, uu____2040)  in
                   (uu____2036, [])  in
                 FStar_Syntax_Syntax.Sig_let uu____2032  in
               {
                 FStar_Syntax_Syntax.sigel = uu____2031;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___159_2030.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___159_2030.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___159_2030.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___159_2030.FStar_Syntax_Syntax.sigattrs)
               }  in
             let uu____2052 = extract_sig g always_fail  in
             (match uu____2052 with
              | (g1,mlm) ->
                  let uu____2063 =
                    FStar_Util.find_map quals
                      (fun uu___156_2067  ->
                         match uu___156_2067 with
                         | FStar_Syntax_Syntax.Discriminator l ->
                             FStar_Pervasives_Native.Some l
                         | uu____2070 -> FStar_Pervasives_Native.None)
                     in
                  (match uu____2063 with
                   | FStar_Pervasives_Native.Some l ->
                       let uu____2075 =
                         let uu____2077 =
                           let uu____2078 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng
                              in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____2078  in
                         let uu____2079 =
                           let uu____2081 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l
                              in
                           [uu____2081]  in
                         uu____2077 :: uu____2079  in
                       (g1, uu____2075)
                   | uu____2083 ->
                       let uu____2085 =
                         FStar_Util.find_map quals
                           (fun uu___157_2090  ->
                              match uu___157_2090 with
                              | FStar_Syntax_Syntax.Projector (l,uu____2093)
                                  -> FStar_Pervasives_Native.Some l
                              | uu____2094 -> FStar_Pervasives_Native.None)
                          in
                       (match uu____2085 with
                        | FStar_Pervasives_Native.Some uu____2098 -> (g1, [])
                        | uu____2100 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____2106 = FStar_Extraction_ML_Term.term_as_mlexpr g e  in
           (match uu____2106 with
            | (ml_main,uu____2114,uu____2115) ->
                let uu____2116 =
                  let uu____2118 =
                    let uu____2119 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng
                       in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____2119  in
                  [uu____2118; FStar_Extraction_ML_Syntax.MLM_Top ml_main]
                   in
                (g, uu____2116))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____2121 ->
           failwith "impossible -- removed by tc.fs"
       | FStar_Syntax_Syntax.Sig_assume uu____2125 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____2130 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____2132 -> (g, [])
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (if p = FStar_Syntax_Syntax.LightOff
            then FStar_Options.set_ml_ish ()
            else ();
            (g, [])))
  
let extract_iface :
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.modul -> env_t =
  fun g  ->
    fun m  ->
      let uu____2152 =
        FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____2152 FStar_Pervasives_Native.fst
  
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
      (let uu____2180 = FStar_Options.debug_any ()  in
       if uu____2180
       then
         let uu____2181 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name  in
         FStar_Util.print1 "Extracting module %s\n" uu____2181
       else ());
      (let uu____2183 = FStar_Options.restore_cmd_line_options true  in
       let name =
         FStar_Extraction_ML_Syntax.mlpath_of_lident
           m.FStar_Syntax_Syntax.name
          in
       let g1 =
         let uu___160_2186 = g  in
         {
           FStar_Extraction_ML_UEnv.tcenv =
             (uu___160_2186.FStar_Extraction_ML_UEnv.tcenv);
           FStar_Extraction_ML_UEnv.gamma =
             (uu___160_2186.FStar_Extraction_ML_UEnv.gamma);
           FStar_Extraction_ML_UEnv.tydefs =
             (uu___160_2186.FStar_Extraction_ML_UEnv.tydefs);
           FStar_Extraction_ML_UEnv.currentModule = name
         }  in
       let uu____2187 =
         FStar_Util.fold_map extract_sig g1
           m.FStar_Syntax_Syntax.declarations
          in
       match uu____2187 with
       | (g2,sigs) ->
           let mlm = FStar_List.flatten sigs  in
           let is_kremlin =
             let uu____2204 = FStar_Options.codegen ()  in
             match uu____2204 with
             | FStar_Pervasives_Native.Some "Kremlin" -> true
             | uu____2206 -> false  in
           let uu____2208 =
             (((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
                (is_kremlin ||
                   (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)))
               &&
               (FStar_Options.should_extract
                  (m.FStar_Syntax_Syntax.name).FStar_Ident.str)
              in
           if uu____2208
           then
             ((let uu____2213 =
                 FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name
                  in
               FStar_Util.print1 "Extracted module %s\n" uu____2213);
              (g2,
                [FStar_Extraction_ML_Syntax.MLLib
                   [(name, (FStar_Pervasives_Native.Some ([], mlm)),
                      (FStar_Extraction_ML_Syntax.MLLib []))]]))
           else (g2, []))
  