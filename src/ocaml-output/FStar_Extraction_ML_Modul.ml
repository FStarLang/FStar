open Prims
let fail_exp lid t =
  let uu____20 =
    let uu____25 =
      let uu____26 =
        let uu____45 =
          FStar_Syntax_Syntax.fvar FStar_Parser_Const.failwith_lid
            FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None in
        let uu____46 =
          let uu____49 = FStar_Syntax_Syntax.iarg t in
          let uu____50 =
            let uu____53 =
              let uu____54 =
                let uu____55 =
                  let uu____60 =
                    let uu____61 =
                      let uu____62 =
                        let uu____69 =
                          let uu____70 =
                            let uu____71 =
                              FStar_Syntax_Print.lid_to_string lid in
                            Prims.strcat "Not yet implemented:" uu____71 in
                          FStar_Bytes.string_as_unicode_bytes uu____70 in
                        (uu____69, FStar_Range.dummyRange) in
                      FStar_Const.Const_string uu____62 in
                    FStar_Syntax_Syntax.Tm_constant uu____61 in
                  FStar_Syntax_Syntax.mk uu____60 in
                uu____55 FStar_Pervasives_Native.None FStar_Range.dummyRange in
              FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____54 in
            [uu____53] in
          uu____49 :: uu____50 in
        (uu____45, uu____46) in
      FStar_Syntax_Syntax.Tm_app uu____26 in
    FStar_Syntax_Syntax.mk uu____25 in
  uu____20 FStar_Pervasives_Native.None FStar_Range.dummyRange
let mangle_projector_lid: FStar_Ident.lident -> FStar_Ident.lident =
  fun x  -> x
let lident_as_mlsymbol: FStar_Ident.lident -> Prims.string =
  fun id  -> (id.FStar_Ident.ident).FStar_Ident.idText
let as_pair uu___148_104 =
  match uu___148_104 with
  | a::b::[] -> (a, b)
  | uu____109 -> failwith "Expected a list with 2 elements"
let rec extract_attr:
  FStar_Syntax_Syntax.term ->
    FStar_Extraction_ML_Syntax.tyattr FStar_Pervasives_Native.option
  =
  fun x  ->
    let uu____122 = FStar_Syntax_Subst.compress x in
    match uu____122 with
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
        FStar_Syntax_Syntax.tk = uu____126;
        FStar_Syntax_Syntax.pos = uu____127;
        FStar_Syntax_Syntax.vars = uu____128;_} when
        let uu____133 =
          let uu____134 = FStar_Syntax_Syntax.lid_of_fv fv in
          FStar_Ident.string_of_lid uu____134 in
        uu____133 = "FStar.Pervasives.PpxDerivingShow" ->
        FStar_Pervasives_Native.Some
          FStar_Extraction_ML_Syntax.PpxDerivingShow
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.tk = uu____136;
             FStar_Syntax_Syntax.pos = uu____137;
             FStar_Syntax_Syntax.vars = uu____138;_},({
                                                        FStar_Syntax_Syntax.n
                                                          =
                                                          FStar_Syntax_Syntax.Tm_constant
                                                          (FStar_Const.Const_string
                                                          (data,uu____140));
                                                        FStar_Syntax_Syntax.tk
                                                          = uu____141;
                                                        FStar_Syntax_Syntax.pos
                                                          = uu____142;
                                                        FStar_Syntax_Syntax.vars
                                                          = uu____143;_},uu____144)::[]);
        FStar_Syntax_Syntax.tk = uu____145;
        FStar_Syntax_Syntax.pos = uu____146;
        FStar_Syntax_Syntax.vars = uu____147;_} when
        let uu____198 =
          let uu____199 = FStar_Syntax_Syntax.lid_of_fv fv in
          FStar_Ident.string_of_lid uu____199 in
        uu____198 = "FStar.Pervasives.PpxDerivingShowConstant" ->
        FStar_Pervasives_Native.Some
          (FStar_Extraction_ML_Syntax.PpxDerivingShowConstant
             (FStar_Util.string_of_unicode data))
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_meta (x1,uu____201);
        FStar_Syntax_Syntax.tk = uu____202;
        FStar_Syntax_Syntax.pos = uu____203;
        FStar_Syntax_Syntax.vars = uu____204;_} -> extract_attr x1
    | a -> FStar_Pervasives_Native.None
let extract_attrs:
  FStar_Syntax_Syntax.term Prims.list ->
    FStar_Extraction_ML_Syntax.tyattr Prims.list
  = fun attrs  -> FStar_List.choose extract_attr attrs
let binders_as_mlty_binders env bs =
  FStar_Util.fold_map
    (fun env1  ->
       fun uu____280  ->
         match uu____280 with
         | (bv,uu____294) ->
             let uu____295 =
               let uu____296 =
                 let uu____299 =
                   let uu____300 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv in
                   FStar_Extraction_ML_Syntax.MLTY_Var uu____300 in
                 FStar_Pervasives_Native.Some uu____299 in
               FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____296 in
             let uu____301 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv in
             (uu____295, uu____301)) env bs
let extract_typ_abbrev:
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
            let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            let def1 =
              let uu____346 =
                let uu____347 = FStar_Syntax_Subst.compress def in
                FStar_All.pipe_right uu____347 FStar_Syntax_Util.unmeta in
              FStar_All.pipe_right uu____346 FStar_Syntax_Util.un_uinst in
            let def2 =
              match def1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_abs uu____349 ->
                  FStar_Extraction_ML_Term.normalize_abs def1
              | uu____368 -> def1 in
            let uu____369 =
              match def2.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____380) ->
                  FStar_Syntax_Subst.open_term bs body
              | uu____405 -> ([], def2) in
            match uu____369 with
            | (bs,body) ->
                let assumed =
                  FStar_Util.for_some
                    (fun uu___149_426  ->
                       match uu___149_426 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____427 -> false) quals in
                let uu____428 = binders_as_mlty_binders env bs in
                (match uu____428 with
                 | (env1,ml_bs) ->
                     let body1 =
                       let uu____460 =
                         FStar_Extraction_ML_Term.term_as_mlty env1 body in
                       FStar_All.pipe_right uu____460
                         (FStar_Extraction_ML_Util.eraseTypeDeep
                            (FStar_Extraction_ML_Util.udelta_unfold env1)) in
                     let mangled_projector =
                       let uu____464 =
                         FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___150_469  ->
                                 match uu___150_469 with
                                 | FStar_Syntax_Syntax.Projector uu____470 ->
                                     true
                                 | uu____475 -> false)) in
                       if uu____464
                       then
                         let mname = mangle_projector_lid lid in
                         FStar_Pervasives_Native.Some
                           ((mname.FStar_Ident.ident).FStar_Ident.idText)
                       else FStar_Pervasives_Native.None in
                     let attrs1 = extract_attrs attrs in
                     let td =
                       let uu____510 =
                         let uu____535 = lident_as_mlsymbol lid in
                         (assumed, uu____535, mangled_projector, ml_bs,
                           attrs1,
                           (FStar_Pervasives_Native.Some
                              (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1))) in
                       [uu____510] in
                     let def3 =
                       let uu____599 =
                         let uu____600 =
                           FStar_Extraction_ML_Util.mlloc_of_range
                             (FStar_Ident.range_of_lid lid) in
                         FStar_Extraction_ML_Syntax.MLM_Loc uu____600 in
                       [uu____599; FStar_Extraction_ML_Syntax.MLM_Ty td] in
                     let env2 =
                       let uu____602 =
                         FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___151_606  ->
                                 match uu___151_606 with
                                 | FStar_Syntax_Syntax.Assumption  -> true
                                 | FStar_Syntax_Syntax.New  -> true
                                 | uu____607 -> false)) in
                       if uu____602
                       then FStar_Extraction_ML_UEnv.extend_type_name env1 fv
                       else FStar_Extraction_ML_UEnv.extend_tydef env1 fv td in
                     (env2, def3))
type data_constructor =
  {
  dname: FStar_Ident.lident;
  dtyp: FStar_Syntax_Syntax.typ;}
let __proj__Mkdata_constructor__item__dname:
  data_constructor -> FStar_Ident.lident =
  fun projectee  ->
    match projectee with
    | { dname = __fname__dname; dtyp = __fname__dtyp;_} -> __fname__dname
let __proj__Mkdata_constructor__item__dtyp:
  data_constructor -> FStar_Syntax_Syntax.typ =
  fun projectee  ->
    match projectee with
    | { dname = __fname__dname; dtyp = __fname__dtyp;_} -> __fname__dtyp
type inductive_family =
  {
  iname: FStar_Ident.lident;
  iparams: FStar_Syntax_Syntax.binders;
  ityp: FStar_Syntax_Syntax.term;
  idatas: data_constructor Prims.list;
  iquals: FStar_Syntax_Syntax.qualifier Prims.list;
  iattrs: FStar_Extraction_ML_Syntax.tyattrs;}
let __proj__Mkinductive_family__item__iname:
  inductive_family -> FStar_Ident.lident =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; iattrs = __fname__iattrs;_} ->
        __fname__iname
let __proj__Mkinductive_family__item__iparams:
  inductive_family -> FStar_Syntax_Syntax.binders =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; iattrs = __fname__iattrs;_} ->
        __fname__iparams
let __proj__Mkinductive_family__item__ityp:
  inductive_family -> FStar_Syntax_Syntax.term =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; iattrs = __fname__iattrs;_} ->
        __fname__ityp
let __proj__Mkinductive_family__item__idatas:
  inductive_family -> data_constructor Prims.list =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; iattrs = __fname__iattrs;_} ->
        __fname__idatas
let __proj__Mkinductive_family__item__iquals:
  inductive_family -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; iattrs = __fname__iattrs;_} ->
        __fname__iquals
let __proj__Mkinductive_family__item__iattrs:
  inductive_family -> FStar_Extraction_ML_Syntax.tyattrs =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; iattrs = __fname__iattrs;_} ->
        __fname__iattrs
let print_ifamily: inductive_family -> Prims.unit =
  fun i  ->
    let uu____755 = FStar_Syntax_Print.lid_to_string i.iname in
    let uu____756 = FStar_Syntax_Print.binders_to_string " " i.iparams in
    let uu____757 = FStar_Syntax_Print.term_to_string i.ityp in
    let uu____758 =
      let uu____759 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let uu____770 = FStar_Syntax_Print.lid_to_string d.dname in
                let uu____771 =
                  let uu____772 = FStar_Syntax_Print.term_to_string d.dtyp in
                  Prims.strcat " : " uu____772 in
                Prims.strcat uu____770 uu____771)) in
      FStar_All.pipe_right uu____759 (FStar_String.concat "\n\t\t") in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____755 uu____756 uu____757
      uu____758
let bundle_as_inductive_families env ses quals attrs =
  let uu____816 =
    FStar_Util.fold_map
      (fun env1  ->
         fun se  ->
           match se.FStar_Syntax_Syntax.sigel with
           | FStar_Syntax_Syntax.Sig_inductive_typ (l,_us,bs,t,_mut_i,datas)
               ->
               let uu____863 = FStar_Syntax_Subst.open_term bs t in
               (match uu____863 with
                | (bs1,t1) ->
                    let datas1 =
                      FStar_All.pipe_right ses
                        (FStar_List.collect
                           (fun se1  ->
                              match se1.FStar_Syntax_Syntax.sigel with
                              | FStar_Syntax_Syntax.Sig_datacon
                                  (d,uu____902,t2,l',nparams,uu____906) when
                                  FStar_Ident.lid_equals l l' ->
                                  let uu____911 =
                                    FStar_Syntax_Util.arrow_formals t2 in
                                  (match uu____911 with
                                   | (bs',body) ->
                                       let uu____950 =
                                         FStar_Util.first_N
                                           (FStar_List.length bs1) bs' in
                                       (match uu____950 with
                                        | (bs_params,rest) ->
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____1021  ->
                                                   fun uu____1022  ->
                                                     match (uu____1021,
                                                             uu____1022)
                                                     with
                                                     | ((b',uu____1040),
                                                        (b,uu____1042)) ->
                                                         let uu____1051 =
                                                           let uu____1060 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (b', uu____1060) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____1051)
                                                bs_params bs1 in
                                            let t3 =
                                              let uu____1062 =
                                                let uu____1067 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    body in
                                                FStar_Syntax_Util.arrow rest
                                                  uu____1067 in
                                              FStar_All.pipe_right uu____1062
                                                (FStar_Syntax_Subst.subst
                                                   subst1) in
                                            [{ dname = d; dtyp = t3 }]))
                              | uu____1076 -> [])) in
                    let attrs1 =
                      extract_attrs
                        (FStar_List.append se.FStar_Syntax_Syntax.sigattrs
                           attrs) in
                    let env2 =
                      let uu____1081 =
                        FStar_Syntax_Syntax.lid_as_fv l
                          FStar_Syntax_Syntax.Delta_constant
                          FStar_Pervasives_Native.None in
                      FStar_Extraction_ML_UEnv.extend_type_name env1
                        uu____1081 in
                    (env2,
                      [{
                         iname = l;
                         iparams = bs1;
                         ityp = t1;
                         idatas = datas1;
                         iquals = (se.FStar_Syntax_Syntax.sigquals);
                         iattrs = attrs1
                       }]))
           | uu____1084 -> (env1, [])) env ses in
  match uu____816 with | (env1,ifams) -> (env1, (FStar_List.flatten ifams))
type env_t = FStar_Extraction_ML_UEnv.env
let extract_bundle:
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t,FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let extract_ctor ml_tyvars env1 ctor =
        let mlt =
          let uu____1170 =
            FStar_Extraction_ML_Term.term_as_mlty env1 ctor.dtyp in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env1) uu____1170 in
        let steps =
          [FStar_TypeChecker_Normalize.Inlining;
          FStar_TypeChecker_Normalize.UnfoldUntil
            FStar_Syntax_Syntax.Delta_constant;
          FStar_TypeChecker_Normalize.EraseUniverses;
          FStar_TypeChecker_Normalize.AllowUnboundUniverses] in
        let names1 =
          let uu____1177 =
            let uu____1178 =
              let uu____1183 =
                FStar_TypeChecker_Normalize.normalize steps
                  env1.FStar_Extraction_ML_UEnv.tcenv ctor.dtyp in
              FStar_Syntax_Subst.compress uu____1183 in
            uu____1178.FStar_Syntax_Syntax.n in
          match uu____1177 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,uu____1187) ->
              FStar_List.map
                (fun uu____1217  ->
                   match uu____1217 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____1223;
                        FStar_Syntax_Syntax.sort = uu____1224;_},uu____1225)
                       -> ppname.FStar_Ident.idText) bs
          | uu____1230 -> [] in
        let tys = (ml_tyvars, mlt) in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp in
        let uu____1249 =
          let uu____1250 =
            FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false in
          FStar_Pervasives_Native.fst uu____1250 in
        let uu____1255 =
          let uu____1266 = lident_as_mlsymbol ctor.dname in
          let uu____1267 =
            let uu____1274 = FStar_Extraction_ML_Util.argTypes mlt in
            FStar_List.zip names1 uu____1274 in
          (uu____1266, uu____1267) in
        (uu____1249, uu____1255) in
      let extract_one_family env1 ind =
        let uu____1326 = binders_as_mlty_binders env1 ind.iparams in
        match uu____1326 with
        | (env2,vars) ->
            let uu____1377 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor vars) env2) in
            (match uu____1377 with
             | (env3,ctors) ->
                 let uu____1474 = FStar_Syntax_Util.arrow_formals ind.ityp in
                 (match uu____1474 with
                  | (indices,uu____1516) ->
                      let ml_params =
                        let uu____1544 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____1575  ->
                                    let uu____1580 =
                                      let uu____1581 =
                                        FStar_Util.string_of_int i in
                                      Prims.strcat "'dummyV" uu____1581 in
                                    (uu____1580, (Prims.parse_int "0")))) in
                        FStar_List.append vars uu____1544 in
                      let tbody =
                        let uu____1587 =
                          FStar_Util.find_opt
                            (fun uu___152_1592  ->
                               match uu___152_1592 with
                               | FStar_Syntax_Syntax.RecordType uu____1593 ->
                                   true
                               | uu____1602 -> false) ind.iquals in
                        match uu____1587 with
                        | FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____1613 = FStar_List.hd ctors in
                            (match uu____1613 with
                             | (uu____1634,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id  ->
                                        fun uu____1673  ->
                                          match uu____1673 with
                                          | (uu____1682,ty) ->
                                              let lid =
                                                FStar_Ident.lid_of_ids
                                                  (FStar_List.append ns [id]) in
                                              let uu____1685 =
                                                lident_as_mlsymbol lid in
                                              (uu____1685, ty)) ids c_ty in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____1686 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors in
                      let uu____1689 =
                        let uu____1712 = lident_as_mlsymbol ind.iname in
                        (false, uu____1712, FStar_Pervasives_Native.None,
                          ml_params, (ind.iattrs),
                          (FStar_Pervasives_Native.Some tbody)) in
                      (env3, uu____1689))) in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____1754,t,uu____1756,uu____1757,uu____1758);
            FStar_Syntax_Syntax.sigrng = uu____1759;
            FStar_Syntax_Syntax.sigquals = uu____1760;
            FStar_Syntax_Syntax.sigmeta = uu____1761;
            FStar_Syntax_Syntax.sigattrs = uu____1762;_}::[],uu____1763),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____1780 = extract_ctor [] env { dname = l; dtyp = t } in
          (match uu____1780 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____1830),quals) ->
          let uu____1844 =
            bundle_as_inductive_families env ses quals
              se.FStar_Syntax_Syntax.sigattrs in
          (match uu____1844 with
           | (env1,ifams) ->
               let uu____1865 =
                 FStar_Util.fold_map extract_one_family env1 ifams in
               (match uu____1865 with
                | (env2,td) -> (env2, [FStar_Extraction_ML_Syntax.MLM_Ty td])))
      | uu____1974 -> failwith "Unexpected signature element"
let rec extract_sig:
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t,FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun g  ->
    fun se  ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u  ->
           let uu____2011 = FStar_Syntax_Print.sigelt_to_string se in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____2011);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____2018 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____2027 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____2044 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
           ->
           let extend_env g1 lid ml_name tm tysc =
             let uu____2082 =
               let uu____2087 =
                 FStar_Syntax_Syntax.lid_as_fv lid
                   FStar_Syntax_Syntax.Delta_equational
                   FStar_Pervasives_Native.None in
               FStar_Extraction_ML_UEnv.extend_fv' g1 uu____2087 ml_name tysc
                 false false in
             match uu____2082 with
             | (g2,mangled_name) ->
                 ((let uu____2095 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          g2.FStar_Extraction_ML_UEnv.tcenv)
                       (FStar_Options.Other "ExtractionReify") in
                   if uu____2095
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
                     } in
                   (g2,
                     (FStar_Extraction_ML_Syntax.MLM_Let
                        (FStar_Extraction_ML_Syntax.NonRec, [], [lb]))))) in
           let rec extract_fv tm =
             (let uu____2111 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify") in
              if uu____2111
              then
                let uu____2112 = FStar_Syntax_Print.term_to_string tm in
                FStar_Util.print1 "extract_fv term: %s\n" uu____2112
              else ());
             (let uu____2114 =
                let uu____2115 = FStar_Syntax_Subst.compress tm in
                uu____2115.FStar_Syntax_Syntax.n in
              match uu____2114 with
              | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____2125) ->
                  extract_fv tm1
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let mlp =
                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  let uu____2136 =
                    let uu____2145 = FStar_Extraction_ML_UEnv.lookup_fv g fv in
                    FStar_All.pipe_left FStar_Util.right uu____2145 in
                  (match uu____2136 with
                   | (uu____2202,uu____2203,tysc,uu____2205) ->
                       let uu____2206 =
                         FStar_All.pipe_left
                           (FStar_Extraction_ML_Syntax.with_ty
                              FStar_Extraction_ML_Syntax.MLTY_Top)
                           (FStar_Extraction_ML_Syntax.MLE_Name mlp) in
                       (uu____2206, tysc))
              | uu____2207 -> failwith "Not an fv") in
           let extract_action g1 a =
             (let uu____2233 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g1.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify") in
              if uu____2233
              then
                let uu____2234 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_typ in
                let uu____2235 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_defn in
                FStar_Util.print2 "Action type %s and term %s\n" uu____2234
                  uu____2235
              else ());
             (let uu____2237 = FStar_Extraction_ML_UEnv.action_name ed a in
              match uu____2237 with
              | (a_nm,a_lid) ->
                  let lbname =
                    let uu____2253 =
                      FStar_Syntax_Syntax.new_bv
                        (FStar_Pervasives_Native.Some
                           ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                        FStar_Syntax_Syntax.tun in
                    FStar_Util.Inl uu____2253 in
                  let lb =
                    FStar_Syntax_Syntax.mk_lb
                      (lbname, (a.FStar_Syntax_Syntax.action_univs),
                        FStar_Parser_Const.effect_Tot_lid,
                        (a.FStar_Syntax_Syntax.action_typ),
                        (a.FStar_Syntax_Syntax.action_defn)) in
                  let lbs = (false, [lb]) in
                  let action_lb =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_let
                         (lbs, FStar_Syntax_Util.exp_false_bool))
                      FStar_Pervasives_Native.None
                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                  let uu____2283 =
                    FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb in
                  (match uu____2283 with
                   | (a_let,uu____2295,ty) ->
                       ((let uu____2298 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug
                                g1.FStar_Extraction_ML_UEnv.tcenv)
                             (FStar_Options.Other "ExtractionReify") in
                         if uu____2298
                         then
                           let uu____2299 =
                             FStar_Extraction_ML_Code.string_of_mlexpr a_nm
                               a_let in
                           FStar_Util.print1 "Extracted action term: %s\n"
                             uu____2299
                         else ());
                        (let uu____2301 =
                           match a_let.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_Let
                               ((uu____2310,uu____2311,mllb::[]),uu____2313)
                               ->
                               (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                                with
                                | FStar_Pervasives_Native.Some tysc ->
                                    ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                      tysc)
                                | FStar_Pervasives_Native.None  ->
                                    failwith "No type scheme")
                           | uu____2333 -> failwith "Impossible" in
                         match uu____2301 with
                         | (exp,tysc) ->
                             ((let uu____2345 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug
                                      g1.FStar_Extraction_ML_UEnv.tcenv)
                                   (FStar_Options.Other "ExtractionReify") in
                               if uu____2345
                               then
                                 ((let uu____2347 =
                                     FStar_Extraction_ML_Code.string_of_mlty
                                       a_nm
                                       (FStar_Pervasives_Native.snd tysc) in
                                   FStar_Util.print1
                                     "Extracted action type: %s\n" uu____2347);
                                  FStar_List.iter
                                    (fun x  ->
                                       FStar_Util.print1 "and binders: %s\n"
                                         (FStar_Pervasives_Native.fst x))
                                    (FStar_Pervasives_Native.fst tysc))
                               else ());
                              extend_env g1 a_lid a_nm exp tysc))))) in
           let uu____2359 =
             let uu____2364 =
               extract_fv
                 (FStar_Pervasives_Native.snd
                    ed.FStar_Syntax_Syntax.return_repr) in
             match uu____2364 with
             | (return_tm,ty_sc) ->
                 let uu____2377 =
                   FStar_Extraction_ML_UEnv.monad_op_name ed "return" in
                 (match uu____2377 with
                  | (return_nm,return_lid) ->
                      extend_env g return_lid return_nm return_tm ty_sc) in
           (match uu____2359 with
            | (g1,return_decl) ->
                let uu____2396 =
                  let uu____2401 =
                    extract_fv
                      (FStar_Pervasives_Native.snd
                         ed.FStar_Syntax_Syntax.bind_repr) in
                  match uu____2401 with
                  | (bind_tm,ty_sc) ->
                      let uu____2414 =
                        FStar_Extraction_ML_UEnv.monad_op_name ed "bind" in
                      (match uu____2414 with
                       | (bind_nm,bind_lid) ->
                           extend_env g1 bind_lid bind_nm bind_tm ty_sc) in
                (match uu____2396 with
                 | (g2,bind_decl) ->
                     let uu____2433 =
                       FStar_Util.fold_map extract_action g2
                         ed.FStar_Syntax_Syntax.actions in
                     (match uu____2433 with
                      | (g3,actions) ->
                          (g3,
                            (FStar_List.append [return_decl; bind_decl]
                               actions)))))
       | FStar_Syntax_Syntax.Sig_new_effect uu____2454 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____2458,t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let attrs = se.FStar_Syntax_Syntax.sigattrs in
           let uu____2466 =
             let uu____2467 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___153_2471  ->
                       match uu___153_2471 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____2472 -> false)) in
             Prims.op_Negation uu____2467 in
           if uu____2466
           then (g, [])
           else
             (let uu____2482 = FStar_Syntax_Util.arrow_formals t in
              match uu____2482 with
              | (bs,uu____2504) ->
                  let fv =
                    FStar_Syntax_Syntax.lid_as_fv lid
                      FStar_Syntax_Syntax.Delta_constant
                      FStar_Pervasives_Native.None in
                  let uu____2526 =
                    FStar_Syntax_Util.abs bs FStar_TypeChecker_Common.t_unit
                      FStar_Pervasives_Native.None in
                  extract_typ_abbrev g fv quals attrs uu____2526)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____2528) when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____2544 =
             let uu____2553 =
               FStar_TypeChecker_Env.open_universes_in
                 g.FStar_Extraction_ML_UEnv.tcenv
                 lb.FStar_Syntax_Syntax.lbunivs
                 [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp] in
             match uu____2553 with
             | (tcenv,uu____2583,def_typ) ->
                 let uu____2589 = as_pair def_typ in (tcenv, uu____2589) in
           (match uu____2544 with
            | (tcenv,(lbdef,lbtyp)) ->
                let lbtyp1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.UnfoldUntil
                      FStar_Syntax_Syntax.Delta_constant] tcenv lbtyp in
                let lbdef1 =
                  FStar_TypeChecker_Normalize.eta_expand_with_type tcenv
                    lbdef lbtyp1 in
                let uu____2613 =
                  FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                extract_typ_abbrev g uu____2613 quals
                  se.FStar_Syntax_Syntax.sigattrs lbdef1)
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____2615) ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs in
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let elet =
             FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_let
                  (lbs, FStar_Syntax_Util.exp_false_bool))
               FStar_Pervasives_Native.None se.FStar_Syntax_Syntax.sigrng in
           let tactic_registration_decl =
             let is_tactic_decl tac_lid h =
               match h.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_uinst (h',uu____2646) ->
                   let uu____2655 =
                     let uu____2656 = FStar_Syntax_Subst.compress h' in
                     uu____2656.FStar_Syntax_Syntax.n in
                   (match uu____2655 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.tactic_lid
                        ->
                        let uu____2662 =
                          let uu____2663 =
                            FStar_Extraction_ML_Syntax.string_of_mlpath
                              g.FStar_Extraction_ML_UEnv.currentModule in
                          FStar_Util.starts_with uu____2663 "FStar.Tactics" in
                        Prims.op_Negation uu____2662
                    | uu____2664 -> false)
               | uu____2665 -> false in
             let mk_registration tac_lid assm_lid t bs =
               let h =
                 let uu____2692 =
                   let uu____2693 =
                     let uu____2694 =
                       FStar_Ident.lid_of_str
                         "FStar_Tactics_Native.register_tactic" in
                     FStar_Extraction_ML_Syntax.mlpath_of_lident uu____2694 in
                   FStar_Extraction_ML_Syntax.MLE_Name uu____2693 in
                 FStar_All.pipe_left
                   (FStar_Extraction_ML_Syntax.with_ty
                      FStar_Extraction_ML_Syntax.MLTY_Top) uu____2692 in
               let lid_arg =
                 let uu____2696 =
                   let uu____2697 = FStar_Ident.string_of_lid assm_lid in
                   FStar_Extraction_ML_Syntax.MLC_String uu____2697 in
                 FStar_Extraction_ML_Syntax.MLE_Const uu____2696 in
               let tac_arity = FStar_List.length bs in
               let arity =
                 let uu____2704 =
                   let uu____2705 =
                     let uu____2706 =
                       FStar_Util.string_of_int
                         (tac_arity + (Prims.parse_int "1")) in
                     FStar_Ident.lid_of_str uu____2706 in
                   FStar_Extraction_ML_Syntax.mlpath_of_lident uu____2705 in
                 FStar_Extraction_ML_Syntax.MLE_Name uu____2704 in
               let tac_interpretation =
                 FStar_Extraction_ML_Util.mk_interpretation_fun tac_lid
                   lid_arg t bs in
               let app =
                 let uu____2715 =
                   let uu____2716 =
                     let uu____2723 =
                       FStar_List.map
                         (FStar_Extraction_ML_Syntax.with_ty
                            FStar_Extraction_ML_Syntax.MLTY_Top)
                         [lid_arg; arity; tac_interpretation] in
                     (h, uu____2723) in
                   FStar_Extraction_ML_Syntax.MLE_App uu____2716 in
                 FStar_All.pipe_left
                   (FStar_Extraction_ML_Syntax.with_ty
                      FStar_Extraction_ML_Syntax.MLTY_Top) uu____2715 in
               FStar_Extraction_ML_Syntax.MLM_Top app in
             match FStar_Pervasives_Native.snd lbs with
             | hd1::[] ->
                 let uu____2733 =
                   FStar_Syntax_Util.arrow_formals_comp
                     hd1.FStar_Syntax_Syntax.lbtyp in
                 (match uu____2733 with
                  | (bs,comp) ->
                      let t = FStar_Syntax_Util.comp_result comp in
                      let uu____2765 =
                        let uu____2766 = FStar_Syntax_Subst.compress t in
                        uu____2766.FStar_Syntax_Syntax.n in
                      (match uu____2765 with
                       | FStar_Syntax_Syntax.Tm_app (h,args) ->
                           let h1 = FStar_Syntax_Subst.compress h in
                           let tac_lid =
                             let uu____2805 =
                               let uu____2808 =
                                 FStar_Util.right
                                   hd1.FStar_Syntax_Syntax.lbname in
                               uu____2808.FStar_Syntax_Syntax.fv_name in
                             uu____2805.FStar_Syntax_Syntax.v in
                           let assm_lid =
                             let uu____2810 =
                               FStar_All.pipe_left FStar_Ident.id_of_text
                                 (Prims.strcat "__"
                                    (tac_lid.FStar_Ident.ident).FStar_Ident.idText) in
                             FStar_Ident.lid_of_ns_and_id
                               tac_lid.FStar_Ident.ns uu____2810 in
                           let uu____2811 = is_tactic_decl assm_lid h1 in
                           if uu____2811
                           then
                             let uu____2814 =
                               let uu____2815 =
                                 let uu____2816 = FStar_List.hd args in
                                 FStar_Pervasives_Native.fst uu____2816 in
                               mk_registration tac_lid assm_lid uu____2815 bs in
                             [uu____2814]
                           else []
                       | uu____2838 -> []))
             | uu____2839 -> [] in
           let uu____2842 = FStar_Extraction_ML_Term.term_as_mlexpr g elet in
           (match uu____2842 with
            | (ml_let,uu____2856,uu____2857) ->
                (match ml_let.FStar_Extraction_ML_Syntax.expr with
                 | FStar_Extraction_ML_Syntax.MLE_Let
                     ((flavor,uu____2865,bindings),uu____2867) ->
                     let uu____2880 =
                       FStar_List.fold_left2
                         (fun uu____2907  ->
                            fun ml_lb  ->
                              fun uu____2909  ->
                                match (uu____2907, uu____2909) with
                                | ((env,ml_lbs),{
                                                  FStar_Syntax_Syntax.lbname
                                                    = lbname;
                                                  FStar_Syntax_Syntax.lbunivs
                                                    = uu____2931;
                                                  FStar_Syntax_Syntax.lbtyp =
                                                    t;
                                                  FStar_Syntax_Syntax.lbeff =
                                                    uu____2933;
                                                  FStar_Syntax_Syntax.lbdef =
                                                    uu____2934;_})
                                    ->
                                    let lb_lid =
                                      let uu____2960 =
                                        let uu____2963 =
                                          FStar_Util.right lbname in
                                        uu____2963.FStar_Syntax_Syntax.fv_name in
                                      uu____2960.FStar_Syntax_Syntax.v in
                                    let uu____2964 =
                                      let uu____2969 =
                                        FStar_All.pipe_right quals
                                          (FStar_Util.for_some
                                             (fun uu___154_2974  ->
                                                match uu___154_2974 with
                                                | FStar_Syntax_Syntax.Projector
                                                    uu____2975 -> true
                                                | uu____2980 -> false)) in
                                      if uu____2969
                                      then
                                        let mname =
                                          let uu____2986 =
                                            mangle_projector_lid lb_lid in
                                          FStar_All.pipe_right uu____2986
                                            FStar_Extraction_ML_Syntax.mlpath_of_lident in
                                        let uu____2987 =
                                          let uu____2992 =
                                            FStar_Util.right lbname in
                                          let uu____2993 =
                                            FStar_Util.must
                                              ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc in
                                          FStar_Extraction_ML_UEnv.extend_fv'
                                            env uu____2992 mname uu____2993
                                            ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                            false in
                                        match uu____2987 with
                                        | (env1,uu____2999) ->
                                            (env1,
                                              (let uu___159_3001 = ml_lb in
                                               {
                                                 FStar_Extraction_ML_Syntax.mllb_name
                                                   =
                                                   ((FStar_Pervasives_Native.snd
                                                       mname),
                                                     (Prims.parse_int "0"));
                                                 FStar_Extraction_ML_Syntax.mllb_tysc
                                                   =
                                                   (uu___159_3001.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                 FStar_Extraction_ML_Syntax.mllb_add_unit
                                                   =
                                                   (uu___159_3001.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                 FStar_Extraction_ML_Syntax.mllb_def
                                                   =
                                                   (uu___159_3001.FStar_Extraction_ML_Syntax.mllb_def);
                                                 FStar_Extraction_ML_Syntax.print_typ
                                                   =
                                                   (uu___159_3001.FStar_Extraction_ML_Syntax.print_typ)
                                               }))
                                      else
                                        (let uu____3005 =
                                           let uu____3006 =
                                             let uu____3011 =
                                               FStar_Util.must
                                                 ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc in
                                             FStar_Extraction_ML_UEnv.extend_lb
                                               env lbname t uu____3011
                                               ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                               false in
                                           FStar_All.pipe_left
                                             FStar_Pervasives_Native.fst
                                             uu____3006 in
                                         (uu____3005, ml_lb)) in
                                    (match uu____2964 with
                                     | (g1,ml_lb1) ->
                                         (g1, (ml_lb1 :: ml_lbs)))) (g, [])
                         bindings (FStar_Pervasives_Native.snd lbs) in
                     (match uu____2880 with
                      | (g1,ml_lbs') ->
                          let flags =
                            FStar_List.choose
                              (fun uu___155_3046  ->
                                 match uu___155_3046 with
                                 | FStar_Syntax_Syntax.Assumption  ->
                                     FStar_Pervasives_Native.Some
                                       FStar_Extraction_ML_Syntax.Assumed
                                 | FStar_Syntax_Syntax.Private  ->
                                     FStar_Pervasives_Native.Some
                                       FStar_Extraction_ML_Syntax.Private
                                 | FStar_Syntax_Syntax.NoExtract  ->
                                     FStar_Pervasives_Native.Some
                                       FStar_Extraction_ML_Syntax.NoExtract
                                 | uu____3049 -> FStar_Pervasives_Native.None)
                              quals in
                          let flags' =
                            FStar_List.choose
                              (fun uu___156_3063  ->
                                 match uu___156_3063 with
                                 | {
                                     FStar_Syntax_Syntax.n =
                                       FStar_Syntax_Syntax.Tm_constant
                                       (FStar_Const.Const_string
                                       (data,uu____3071));
                                     FStar_Syntax_Syntax.tk = uu____3072;
                                     FStar_Syntax_Syntax.pos = uu____3073;
                                     FStar_Syntax_Syntax.vars = uu____3074;_}
                                     ->
                                     FStar_Pervasives_Native.Some
                                       (FStar_Extraction_ML_Syntax.Attribute
                                          (FStar_Util.string_of_unicode data))
                                 | uu____3083 ->
                                     (FStar_Util.print_warning
                                        "Warning: unrecognized, non-string attribute, bother protz for a better error message";
                                      FStar_Pervasives_Native.None)) attrs in
                          let uu____3089 =
                            let uu____3092 =
                              let uu____3095 =
                                let uu____3096 =
                                  FStar_Extraction_ML_Util.mlloc_of_range
                                    se.FStar_Syntax_Syntax.sigrng in
                                FStar_Extraction_ML_Syntax.MLM_Loc uu____3096 in
                              [uu____3095;
                              FStar_Extraction_ML_Syntax.MLM_Let
                                (flavor, (FStar_List.append flags flags'),
                                  (FStar_List.rev ml_lbs'))] in
                            FStar_List.append uu____3092
                              tactic_registration_decl in
                          (g1, uu____3089))
                 | uu____3103 ->
                     let uu____3104 =
                       let uu____3105 =
                         FStar_Extraction_ML_Code.string_of_mlexpr
                           g.FStar_Extraction_ML_UEnv.currentModule ml_let in
                       FStar_Util.format1
                         "Impossible: Translated a let to a non-let: %s"
                         uu____3105 in
                     failwith uu____3104))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____3113,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____3118 =
             FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption) in
           if uu____3118
           then
             let always_fail =
               let imp =
                 let uu____3129 = FStar_Syntax_Util.arrow_formals t in
                 match uu____3129 with
                 | ([],t1) ->
                     let b =
                       let uu____3164 =
                         FStar_Syntax_Syntax.gen_bv "_"
                           FStar_Pervasives_Native.None t1 in
                       FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                         uu____3164 in
                     let uu____3165 = fail_exp lid t1 in
                     FStar_Syntax_Util.abs [b] uu____3165
                       FStar_Pervasives_Native.None
                 | (bs,t1) ->
                     let uu____3188 = fail_exp lid t1 in
                     FStar_Syntax_Util.abs bs uu____3188
                       FStar_Pervasives_Native.None in
               let uu___160_3189 = se in
               let uu____3190 =
                 let uu____3191 =
                   let uu____3198 =
                     let uu____3205 =
                       let uu____3208 =
                         let uu____3209 =
                           let uu____3214 =
                             FStar_Syntax_Syntax.lid_as_fv lid
                               FStar_Syntax_Syntax.Delta_constant
                               FStar_Pervasives_Native.None in
                           FStar_Util.Inr uu____3214 in
                         {
                           FStar_Syntax_Syntax.lbname = uu____3209;
                           FStar_Syntax_Syntax.lbunivs = [];
                           FStar_Syntax_Syntax.lbtyp = t;
                           FStar_Syntax_Syntax.lbeff =
                             FStar_Parser_Const.effect_ML_lid;
                           FStar_Syntax_Syntax.lbdef = imp
                         } in
                       [uu____3208] in
                     (false, uu____3205) in
                   (uu____3198, []) in
                 FStar_Syntax_Syntax.Sig_let uu____3191 in
               {
                 FStar_Syntax_Syntax.sigel = uu____3190;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___160_3189.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___160_3189.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___160_3189.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___160_3189.FStar_Syntax_Syntax.sigattrs)
               } in
             let uu____3225 = extract_sig g always_fail in
             (match uu____3225 with
              | (g1,mlm) ->
                  let uu____3244 =
                    FStar_Util.find_map quals
                      (fun uu___157_3249  ->
                         match uu___157_3249 with
                         | FStar_Syntax_Syntax.Discriminator l ->
                             FStar_Pervasives_Native.Some l
                         | uu____3253 -> FStar_Pervasives_Native.None) in
                  (match uu____3244 with
                   | FStar_Pervasives_Native.Some l ->
                       let uu____3261 =
                         let uu____3264 =
                           let uu____3265 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____3265 in
                         let uu____3266 =
                           let uu____3269 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l in
                           [uu____3269] in
                         uu____3264 :: uu____3266 in
                       (g1, uu____3261)
                   | uu____3272 ->
                       let uu____3275 =
                         FStar_Util.find_map quals
                           (fun uu___158_3281  ->
                              match uu___158_3281 with
                              | FStar_Syntax_Syntax.Projector (l,uu____3285)
                                  -> FStar_Pervasives_Native.Some l
                              | uu____3286 -> FStar_Pervasives_Native.None) in
                       (match uu____3275 with
                        | FStar_Pervasives_Native.Some uu____3293 -> (g1, [])
                        | uu____3296 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____3305 = FStar_Extraction_ML_Term.term_as_mlexpr g e in
           (match uu____3305 with
            | (ml_main,uu____3319,uu____3320) ->
                let uu____3321 =
                  let uu____3324 =
                    let uu____3325 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____3325 in
                  [uu____3324; FStar_Extraction_ML_Syntax.MLM_Top ml_main] in
                (g, uu____3321))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____3328 ->
           failwith "impossible -- removed by tc.fs"
       | FStar_Syntax_Syntax.Sig_assume uu____3335 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____3344 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____3347 -> (g, [])
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (if p = FStar_Syntax_Syntax.LightOff
            then FStar_Options.set_ml_ish ()
            else ();
            (g, [])))
let extract_iface:
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.modul -> env_t =
  fun g  ->
    fun m  ->
      let uu____3375 =
        FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____3375 FStar_Pervasives_Native.fst
let extract:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Extraction_ML_UEnv.env,FStar_Extraction_ML_Syntax.mllib
                                      Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun g  ->
    fun m  ->
      FStar_Syntax_Syntax.reset_gensym ();
      (let uu____3420 = FStar_Options.debug_any () in
       if uu____3420
       then
         let uu____3421 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
         FStar_Util.print1 "Extracting module %s\n" uu____3421
       else ());
      (let uu____3423 = FStar_Options.restore_cmd_line_options true in
       let name =
         FStar_Extraction_ML_Syntax.mlpath_of_lident
           m.FStar_Syntax_Syntax.name in
       let g1 =
         let uu___161_3426 = g in
         let uu____3427 =
           FStar_TypeChecker_Env.set_current_module
             g.FStar_Extraction_ML_UEnv.tcenv m.FStar_Syntax_Syntax.name in
         {
           FStar_Extraction_ML_UEnv.tcenv = uu____3427;
           FStar_Extraction_ML_UEnv.gamma =
             (uu___161_3426.FStar_Extraction_ML_UEnv.gamma);
           FStar_Extraction_ML_UEnv.tydefs =
             (uu___161_3426.FStar_Extraction_ML_UEnv.tydefs);
           FStar_Extraction_ML_UEnv.type_names =
             (uu___161_3426.FStar_Extraction_ML_UEnv.type_names);
           FStar_Extraction_ML_UEnv.currentModule = name
         } in
       let uu____3428 =
         FStar_Util.fold_map extract_sig g1
           m.FStar_Syntax_Syntax.declarations in
       match uu____3428 with
       | (g2,sigs) ->
           let mlm = FStar_List.flatten sigs in
           let is_kremlin =
             let uu____3457 = FStar_Options.codegen () in
             match uu____3457 with
             | FStar_Pervasives_Native.Some "Kremlin" -> true
             | uu____3460 -> false in
           let uu____3463 =
             (((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
                (is_kremlin ||
                   (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)))
               &&
               (FStar_Options.should_extract
                  (m.FStar_Syntax_Syntax.name).FStar_Ident.str) in
           if uu____3463
           then
             ((let uu____3471 =
                 FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
               FStar_Util.print1 "Extracted module %s\n" uu____3471);
              (g2,
                [FStar_Extraction_ML_Syntax.MLLib
                   [(name, (FStar_Pervasives_Native.Some ([], mlm)),
                      (FStar_Extraction_ML_Syntax.MLLib []))]]))
           else (g2, []))