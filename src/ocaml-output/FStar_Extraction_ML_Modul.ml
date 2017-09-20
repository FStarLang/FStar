open Prims
let fail_exp:
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
                FStar_Pervasives_Native.None in
            let uu____31 =
              let uu____34 = FStar_Syntax_Syntax.iarg t in
              let uu____35 =
                let uu____38 =
                  let uu____39 =
                    let uu____40 =
                      let uu____43 =
                        let uu____44 =
                          let uu____45 =
                            let uu____50 =
                              let uu____51 =
                                FStar_Syntax_Print.lid_to_string lid in
                              Prims.strcat "Not yet implemented:" uu____51 in
                            (uu____50, FStar_Range.dummyRange) in
                          FStar_Const.Const_string uu____45 in
                        FStar_Syntax_Syntax.Tm_constant uu____44 in
                      FStar_Syntax_Syntax.mk uu____43 in
                    uu____40 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange in
                  FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____39 in
                [uu____38] in
              uu____34 :: uu____35 in
            (uu____30, uu____31) in
          FStar_Syntax_Syntax.Tm_app uu____15 in
        FStar_Syntax_Syntax.mk uu____14 in
      uu____11 FStar_Pervasives_Native.None FStar_Range.dummyRange
let mangle_projector_lid: FStar_Ident.lident -> FStar_Ident.lident =
  fun x  -> x
let lident_as_mlsymbol:
  FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlsymbol =
  fun id  -> (id.FStar_Ident.ident).FStar_Ident.idText
let as_pair:
  'Auu____72 .
    'Auu____72 Prims.list ->
      ('Auu____72,'Auu____72) FStar_Pervasives_Native.tuple2
  =
  fun uu___156_82  ->
    match uu___156_82 with
    | a::b::[] -> (a, b)
    | uu____87 -> failwith "Expected a list with 2 elements"
let rec extract_attr:
  FStar_Syntax_Syntax.term ->
    FStar_Extraction_ML_Syntax.tyattr FStar_Pervasives_Native.option
  =
  fun x  ->
    let uu____100 = FStar_Syntax_Subst.compress x in
    match uu____100 with
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
        FStar_Syntax_Syntax.pos = uu____104;
        FStar_Syntax_Syntax.vars = uu____105;_} when
        let uu____108 =
          let uu____109 = FStar_Syntax_Syntax.lid_of_fv fv in
          FStar_Ident.string_of_lid uu____109 in
        uu____108 = "FStar.Pervasives.PpxDerivingShow" ->
        FStar_Pervasives_Native.Some
          FStar_Extraction_ML_Syntax.PpxDerivingShow
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____111;
             FStar_Syntax_Syntax.vars = uu____112;_},({
                                                        FStar_Syntax_Syntax.n
                                                          =
                                                          FStar_Syntax_Syntax.Tm_constant
                                                          (FStar_Const.Const_string
                                                          (s,uu____114));
                                                        FStar_Syntax_Syntax.pos
                                                          = uu____115;
                                                        FStar_Syntax_Syntax.vars
                                                          = uu____116;_},uu____117)::[]);
        FStar_Syntax_Syntax.pos = uu____118;
        FStar_Syntax_Syntax.vars = uu____119;_} when
        let uu____150 =
          let uu____151 = FStar_Syntax_Syntax.lid_of_fv fv in
          FStar_Ident.string_of_lid uu____151 in
        uu____150 = "FStar.Pervasives.PpxDerivingShowConstant" ->
        FStar_Pervasives_Native.Some
          (FStar_Extraction_ML_Syntax.PpxDerivingShowConstant s)
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_meta (x1,uu____153);
        FStar_Syntax_Syntax.pos = uu____154;
        FStar_Syntax_Syntax.vars = uu____155;_} -> extract_attr x1
    | a -> FStar_Pervasives_Native.None
let extract_attrs:
  FStar_Syntax_Syntax.term Prims.list ->
    FStar_Extraction_ML_Syntax.tyattr Prims.list
  = fun attrs  -> FStar_List.choose extract_attr attrs
let binders_as_mlty_binders:
  'Auu____179 .
    FStar_Extraction_ML_UEnv.env ->
      (FStar_Syntax_Syntax.bv,'Auu____179) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Extraction_ML_UEnv.env,Prims.string Prims.list)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bs  ->
      FStar_Util.fold_map
        (fun env1  ->
           fun uu____217  ->
             match uu____217 with
             | (bv,uu____227) ->
                 let uu____228 =
                   let uu____229 =
                     let uu____232 =
                       let uu____233 =
                         FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv in
                       FStar_Extraction_ML_Syntax.MLTY_Var uu____233 in
                     FStar_Pervasives_Native.Some uu____232 in
                   FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____229 in
                 let uu____234 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv in
                 (uu____228, uu____234)) env bs
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
              let uu____271 =
                let uu____272 = FStar_Syntax_Subst.compress def in
                FStar_All.pipe_right uu____272 FStar_Syntax_Util.unmeta in
              FStar_All.pipe_right uu____271 FStar_Syntax_Util.un_uinst in
            let def2 =
              match def1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_abs uu____274 ->
                  FStar_Extraction_ML_Term.normalize_abs def1
              | uu____291 -> def1 in
            let uu____292 =
              match def2.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____303) ->
                  FStar_Syntax_Subst.open_term bs body
              | uu____324 -> ([], def2) in
            match uu____292 with
            | (bs,body) ->
                let assumed =
                  FStar_Util.for_some
                    (fun uu___157_345  ->
                       match uu___157_345 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____346 -> false) quals in
                let uu____347 = binders_as_mlty_binders env bs in
                (match uu____347 with
                 | (env1,ml_bs) ->
                     let body1 =
                       let uu____367 =
                         FStar_Extraction_ML_Term.term_as_mlty env1 body in
                       FStar_All.pipe_right uu____367
                         (FStar_Extraction_ML_Util.eraseTypeDeep
                            (FStar_Extraction_ML_Util.udelta_unfold env1)) in
                     let mangled_projector =
                       let uu____371 =
                         FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___158_376  ->
                                 match uu___158_376 with
                                 | FStar_Syntax_Syntax.Projector uu____377 ->
                                     true
                                 | uu____382 -> false)) in
                       if uu____371
                       then
                         let mname = mangle_projector_lid lid in
                         FStar_Pervasives_Native.Some
                           ((mname.FStar_Ident.ident).FStar_Ident.idText)
                       else FStar_Pervasives_Native.None in
                     let attrs1 = extract_attrs attrs in
                     let td =
                       let uu____413 =
                         let uu____434 = lident_as_mlsymbol lid in
                         (assumed, uu____434, mangled_projector, ml_bs,
                           attrs1,
                           (FStar_Pervasives_Native.Some
                              (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1))) in
                       [uu____413] in
                     let def3 =
                       let uu____486 =
                         let uu____487 =
                           FStar_Extraction_ML_Util.mlloc_of_range
                             (FStar_Ident.range_of_lid lid) in
                         FStar_Extraction_ML_Syntax.MLM_Loc uu____487 in
                       [uu____486; FStar_Extraction_ML_Syntax.MLM_Ty td] in
                     let env2 =
                       let uu____489 =
                         FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___159_493  ->
                                 match uu___159_493 with
                                 | FStar_Syntax_Syntax.Assumption  -> true
                                 | FStar_Syntax_Syntax.New  -> true
                                 | uu____494 -> false)) in
                       if uu____489
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
    let uu____642 = FStar_Syntax_Print.lid_to_string i.iname in
    let uu____643 = FStar_Syntax_Print.binders_to_string " " i.iparams in
    let uu____644 = FStar_Syntax_Print.term_to_string i.ityp in
    let uu____645 =
      let uu____646 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let uu____657 = FStar_Syntax_Print.lid_to_string d.dname in
                let uu____658 =
                  let uu____659 = FStar_Syntax_Print.term_to_string d.dtyp in
                  Prims.strcat " : " uu____659 in
                Prims.strcat uu____657 uu____658)) in
      FStar_All.pipe_right uu____646 (FStar_String.concat "\n\t\t") in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____642 uu____643 uu____644
      uu____645
let bundle_as_inductive_families:
  'Auu____672 .
    FStar_Extraction_ML_UEnv.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'Auu____672 ->
          FStar_Syntax_Syntax.attribute Prims.list ->
            (FStar_Extraction_ML_UEnv.env,inductive_family Prims.list)
              FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun attrs  ->
          let uu____703 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun se  ->
                   match se.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,_us,bs,t,_mut_i,datas) ->
                       let uu____750 = FStar_Syntax_Subst.open_term bs t in
                       (match uu____750 with
                        | (bs1,t1) ->
                            let datas1 =
                              FStar_All.pipe_right ses
                                (FStar_List.collect
                                   (fun se1  ->
                                      match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_datacon
                                          (d,uu____789,t2,l',nparams,uu____793)
                                          when FStar_Ident.lid_equals l l' ->
                                          let uu____798 =
                                            FStar_Syntax_Util.arrow_formals
                                              t2 in
                                          (match uu____798 with
                                           | (bs',body) ->
                                               let uu____831 =
                                                 FStar_Util.first_N
                                                   (FStar_List.length bs1)
                                                   bs' in
                                               (match uu____831 with
                                                | (bs_params,rest) ->
                                                    let subst1 =
                                                      FStar_List.map2
                                                        (fun uu____902  ->
                                                           fun uu____903  ->
                                                             match (uu____902,
                                                                    uu____903)
                                                             with
                                                             | ((b',uu____921),
                                                                (b,uu____923))
                                                                 ->
                                                                 let uu____932
                                                                   =
                                                                   let uu____939
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b in
                                                                   (b',
                                                                    uu____939) in
                                                                 FStar_Syntax_Syntax.NT
                                                                   uu____932)
                                                        bs_params bs1 in
                                                    let t3 =
                                                      let uu____941 =
                                                        let uu____944 =
                                                          FStar_Syntax_Syntax.mk_Total
                                                            body in
                                                        FStar_Syntax_Util.arrow
                                                          rest uu____944 in
                                                      FStar_All.pipe_right
                                                        uu____941
                                                        (FStar_Syntax_Subst.subst
                                                           subst1) in
                                                    [{ dname = d; dtyp = t3 }]))
                                      | uu____949 -> [])) in
                            let attrs1 =
                              extract_attrs
                                (FStar_List.append
                                   se.FStar_Syntax_Syntax.sigattrs attrs) in
                            let env2 =
                              let uu____954 =
                                FStar_Syntax_Syntax.lid_as_fv l
                                  FStar_Syntax_Syntax.Delta_constant
                                  FStar_Pervasives_Native.None in
                              FStar_Extraction_ML_UEnv.extend_type_name env1
                                uu____954 in
                            (env2,
                              [{
                                 iname = l;
                                 iparams = bs1;
                                 ityp = t1;
                                 idatas = datas1;
                                 iquals = (se.FStar_Syntax_Syntax.sigquals);
                                 iattrs = attrs1
                               }]))
                   | uu____957 -> (env1, [])) env ses in
          match uu____703 with
          | (env1,ifams) -> (env1, (FStar_List.flatten ifams))
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
          let uu____1035 =
            FStar_Extraction_ML_Term.term_as_mlty env1 ctor.dtyp in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env1) uu____1035 in
        let steps =
          [FStar_TypeChecker_Normalize.Inlining;
          FStar_TypeChecker_Normalize.UnfoldUntil
            FStar_Syntax_Syntax.Delta_constant;
          FStar_TypeChecker_Normalize.EraseUniverses;
          FStar_TypeChecker_Normalize.AllowUnboundUniverses] in
        let names1 =
          let uu____1042 =
            let uu____1043 =
              let uu____1046 =
                FStar_TypeChecker_Normalize.normalize steps
                  env1.FStar_Extraction_ML_UEnv.tcenv ctor.dtyp in
              FStar_Syntax_Subst.compress uu____1046 in
            uu____1043.FStar_Syntax_Syntax.n in
          match uu____1042 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,uu____1050) ->
              FStar_List.map
                (fun uu____1076  ->
                   match uu____1076 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____1082;
                        FStar_Syntax_Syntax.sort = uu____1083;_},uu____1084)
                       -> ppname.FStar_Ident.idText) bs
          | uu____1087 -> [] in
        let tys = (ml_tyvars, mlt) in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp in
        let uu____1098 =
          let uu____1099 =
            FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false in
          FStar_Pervasives_Native.fst uu____1099 in
        let uu____1104 =
          let uu____1115 = lident_as_mlsymbol ctor.dname in
          let uu____1116 =
            let uu____1123 = FStar_Extraction_ML_Util.argTypes mlt in
            FStar_List.zip names1 uu____1123 in
          (uu____1115, uu____1116) in
        (uu____1098, uu____1104) in
      let extract_one_family env1 ind =
        let uu____1171 = binders_as_mlty_binders env1 ind.iparams in
        match uu____1171 with
        | (env2,vars) ->
            let uu____1206 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor vars) env2) in
            (match uu____1206 with
             | (env3,ctors) ->
                 let uu____1299 = FStar_Syntax_Util.arrow_formals ind.ityp in
                 (match uu____1299 with
                  | (indices,uu____1335) ->
                      let ml_params =
                        let uu____1355 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____1374  ->
                                    let uu____1379 =
                                      FStar_Util.string_of_int i in
                                    Prims.strcat "'dummyV" uu____1379)) in
                        FStar_List.append vars uu____1355 in
                      let tbody =
                        let uu____1381 =
                          FStar_Util.find_opt
                            (fun uu___160_1386  ->
                               match uu___160_1386 with
                               | FStar_Syntax_Syntax.RecordType uu____1387 ->
                                   true
                               | uu____1396 -> false) ind.iquals in
                        match uu____1381 with
                        | FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____1407 = FStar_List.hd ctors in
                            (match uu____1407 with
                             | (uu____1428,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id  ->
                                        fun uu____1467  ->
                                          match uu____1467 with
                                          | (uu____1476,ty) ->
                                              let lid =
                                                FStar_Ident.lid_of_ids
                                                  (FStar_List.append ns [id]) in
                                              let uu____1479 =
                                                lident_as_mlsymbol lid in
                                              (uu____1479, ty)) ids c_ty in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____1480 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors in
                      let uu____1483 =
                        let uu____1502 = lident_as_mlsymbol ind.iname in
                        (false, uu____1502, FStar_Pervasives_Native.None,
                          ml_params, (ind.iattrs),
                          (FStar_Pervasives_Native.Some tbody)) in
                      (env3, uu____1483))) in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____1536,t,uu____1538,uu____1539,uu____1540);
            FStar_Syntax_Syntax.sigrng = uu____1541;
            FStar_Syntax_Syntax.sigquals = uu____1542;
            FStar_Syntax_Syntax.sigmeta = uu____1543;
            FStar_Syntax_Syntax.sigattrs = uu____1544;_}::[],uu____1545),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____1562 = extract_ctor [] env { dname = l; dtyp = t } in
          (match uu____1562 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____1608),quals) ->
          let uu____1622 =
            bundle_as_inductive_families env ses quals
              se.FStar_Syntax_Syntax.sigattrs in
          (match uu____1622 with
           | (env1,ifams) ->
               let uu____1643 =
                 FStar_Util.fold_map extract_one_family env1 ifams in
               (match uu____1643 with
                | (env2,td) -> (env2, [FStar_Extraction_ML_Syntax.MLM_Ty td])))
      | uu____1736 -> failwith "Unexpected signature element"
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
           let uu____1773 = FStar_Syntax_Print.sigelt_to_string se in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____1773);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____1780 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____1789 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____1806 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
           ->
           let extend_env g1 lid ml_name tm tysc =
             let uu____1844 =
               let uu____1849 =
                 FStar_Syntax_Syntax.lid_as_fv lid
                   FStar_Syntax_Syntax.Delta_equational
                   FStar_Pervasives_Native.None in
               FStar_Extraction_ML_UEnv.extend_fv' g1 uu____1849 ml_name tysc
                 false false in
             match uu____1844 with
             | (g2,mangled_name) ->
                 ((let uu____1857 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          g2.FStar_Extraction_ML_UEnv.tcenv)
                       (FStar_Options.Other "ExtractionReify") in
                   if uu____1857
                   then FStar_Util.print1 "Mangled name: %s\n" mangled_name
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
             (let uu____1873 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify") in
              if uu____1873
              then
                let uu____1874 = FStar_Syntax_Print.term_to_string tm in
                FStar_Util.print1 "extract_fv term: %s\n" uu____1874
              else ());
             (let uu____1876 =
                let uu____1877 = FStar_Syntax_Subst.compress tm in
                uu____1877.FStar_Syntax_Syntax.n in
              match uu____1876 with
              | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____1885) ->
                  extract_fv tm1
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let mlp =
                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  let uu____1892 =
                    let uu____1901 = FStar_Extraction_ML_UEnv.lookup_fv g fv in
                    FStar_All.pipe_left FStar_Util.right uu____1901 in
                  (match uu____1892 with
                   | (uu____1958,uu____1959,tysc,uu____1961) ->
                       let uu____1962 =
                         FStar_All.pipe_left
                           (FStar_Extraction_ML_Syntax.with_ty
                              FStar_Extraction_ML_Syntax.MLTY_Top)
                           (FStar_Extraction_ML_Syntax.MLE_Name mlp) in
                       (uu____1962, tysc))
              | uu____1963 -> failwith "Not an fv") in
           let extract_action g1 a =
             (let uu____1989 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g1.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify") in
              if uu____1989
              then
                let uu____1990 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_typ in
                let uu____1991 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_defn in
                FStar_Util.print2 "Action type %s and term %s\n" uu____1990
                  uu____1991
              else ());
             (let uu____1993 = FStar_Extraction_ML_UEnv.action_name ed a in
              match uu____1993 with
              | (a_nm,a_lid) ->
                  let lbname =
                    let uu____2009 =
                      FStar_Syntax_Syntax.new_bv
                        (FStar_Pervasives_Native.Some
                           ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                        FStar_Syntax_Syntax.tun in
                    FStar_Util.Inl uu____2009 in
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
                  let uu____2035 =
                    FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb in
                  (match uu____2035 with
                   | (a_let,uu____2047,ty) ->
                       ((let uu____2050 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug
                                g1.FStar_Extraction_ML_UEnv.tcenv)
                             (FStar_Options.Other "ExtractionReify") in
                         if uu____2050
                         then
                           let uu____2051 =
                             FStar_Extraction_ML_Code.string_of_mlexpr a_nm
                               a_let in
                           FStar_Util.print1 "Extracted action term: %s\n"
                             uu____2051
                         else ());
                        (let uu____2053 =
                           match a_let.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_Let
                               ((uu____2062,uu____2063,mllb::[]),uu____2065)
                               ->
                               (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                                with
                                | FStar_Pervasives_Native.Some tysc ->
                                    ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                      tysc)
                                | FStar_Pervasives_Native.None  ->
                                    failwith "No type scheme")
                           | uu____2085 -> failwith "Impossible" in
                         match uu____2053 with
                         | (exp,tysc) ->
                             ((let uu____2097 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug
                                      g1.FStar_Extraction_ML_UEnv.tcenv)
                                   (FStar_Options.Other "ExtractionReify") in
                               if uu____2097
                               then
                                 ((let uu____2099 =
                                     FStar_Extraction_ML_Code.string_of_mlty
                                       a_nm
                                       (FStar_Pervasives_Native.snd tysc) in
                                   FStar_Util.print1
                                     "Extracted action type: %s\n" uu____2099);
                                  FStar_List.iter
                                    (fun x  ->
                                       FStar_Util.print1 "and binders: %s\n"
                                         x)
                                    (FStar_Pervasives_Native.fst tysc))
                               else ());
                              extend_env g1 a_lid a_nm exp tysc))))) in
           let uu____2103 =
             let uu____2108 =
               extract_fv
                 (FStar_Pervasives_Native.snd
                    ed.FStar_Syntax_Syntax.return_repr) in
             match uu____2108 with
             | (return_tm,ty_sc) ->
                 let uu____2121 =
                   FStar_Extraction_ML_UEnv.monad_op_name ed "return" in
                 (match uu____2121 with
                  | (return_nm,return_lid) ->
                      extend_env g return_lid return_nm return_tm ty_sc) in
           (match uu____2103 with
            | (g1,return_decl) ->
                let uu____2140 =
                  let uu____2145 =
                    extract_fv
                      (FStar_Pervasives_Native.snd
                         ed.FStar_Syntax_Syntax.bind_repr) in
                  match uu____2145 with
                  | (bind_tm,ty_sc) ->
                      let uu____2158 =
                        FStar_Extraction_ML_UEnv.monad_op_name ed "bind" in
                      (match uu____2158 with
                       | (bind_nm,bind_lid) ->
                           extend_env g1 bind_lid bind_nm bind_tm ty_sc) in
                (match uu____2140 with
                 | (g2,bind_decl) ->
                     let uu____2177 =
                       FStar_Util.fold_map extract_action g2
                         ed.FStar_Syntax_Syntax.actions in
                     (match uu____2177 with
                      | (g3,actions) ->
                          (g3,
                            (FStar_List.append [return_decl; bind_decl]
                               actions)))))
       | FStar_Syntax_Syntax.Sig_new_effect uu____2198 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____2202,t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let attrs = se.FStar_Syntax_Syntax.sigattrs in
           let uu____2210 =
             let uu____2211 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___161_2215  ->
                       match uu___161_2215 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____2216 -> false)) in
             Prims.op_Negation uu____2211 in
           if uu____2210
           then (g, [])
           else
             (let uu____2226 = FStar_Syntax_Util.arrow_formals t in
              match uu____2226 with
              | (bs,uu____2246) ->
                  let fv =
                    FStar_Syntax_Syntax.lid_as_fv lid
                      FStar_Syntax_Syntax.Delta_constant
                      FStar_Pervasives_Native.None in
                  let uu____2264 =
                    FStar_Syntax_Util.abs bs FStar_Syntax_Syntax.t_unit
                      FStar_Pervasives_Native.None in
                  extract_typ_abbrev g fv quals attrs uu____2264)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____2266) when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____2282 =
             let uu____2291 =
               FStar_TypeChecker_Env.open_universes_in
                 g.FStar_Extraction_ML_UEnv.tcenv
                 lb.FStar_Syntax_Syntax.lbunivs
                 [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp] in
             match uu____2291 with
             | (tcenv,uu____2315,def_typ) ->
                 let uu____2321 = as_pair def_typ in (tcenv, uu____2321) in
           (match uu____2282 with
            | (tcenv,(lbdef,lbtyp)) ->
                let lbtyp1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.UnfoldUntil
                      FStar_Syntax_Syntax.Delta_constant] tcenv lbtyp in
                let lbdef1 =
                  FStar_TypeChecker_Normalize.eta_expand_with_type tcenv
                    lbdef lbtyp1 in
                let uu____2345 =
                  FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                extract_typ_abbrev g uu____2345 quals
                  se.FStar_Syntax_Syntax.sigattrs lbdef1)
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____2347) ->
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
               | FStar_Syntax_Syntax.Tm_uinst (h',uu____2374) ->
                   let uu____2379 =
                     let uu____2380 = FStar_Syntax_Subst.compress h' in
                     uu____2380.FStar_Syntax_Syntax.n in
                   (match uu____2379 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.tactic_lid
                        ->
                        let uu____2384 =
                          let uu____2385 =
                            FStar_Extraction_ML_Syntax.string_of_mlpath
                              g.FStar_Extraction_ML_UEnv.currentModule in
                          FStar_Util.starts_with uu____2385 "FStar.Tactics" in
                        Prims.op_Negation uu____2384
                    | uu____2386 -> false)
               | uu____2387 -> false in
             let mk_registration tac_lid assm_lid t bs =
               let h =
                 let uu____2416 =
                   let uu____2417 =
                     let uu____2418 =
                       FStar_Ident.lid_of_str
                         "FStar_Tactics_Native.register_tactic" in
                     FStar_Extraction_ML_Syntax.mlpath_of_lident uu____2418 in
                   FStar_Extraction_ML_Syntax.MLE_Name uu____2417 in
                 FStar_All.pipe_left
                   (FStar_Extraction_ML_Syntax.with_ty
                      FStar_Extraction_ML_Syntax.MLTY_Top) uu____2416 in
               let lid_arg =
                 let uu____2420 =
                   let uu____2421 = FStar_Ident.string_of_lid assm_lid in
                   FStar_Extraction_ML_Syntax.MLC_String uu____2421 in
                 FStar_Extraction_ML_Syntax.MLE_Const uu____2420 in
               let tac_arity = FStar_List.length bs in
               let arity =
                 let uu____2428 =
                   let uu____2429 =
                     let uu____2430 =
                       FStar_Util.string_of_int
                         (tac_arity + (Prims.parse_int "1")) in
                     FStar_Ident.lid_of_str uu____2430 in
                   FStar_Extraction_ML_Syntax.mlpath_of_lident uu____2429 in
                 FStar_Extraction_ML_Syntax.MLE_Name uu____2428 in
               let uu____2437 =
                 FStar_Extraction_ML_Util.mk_interpretation_fun tac_lid
                   lid_arg t bs in
               match uu____2437 with
               | FStar_Pervasives_Native.Some tac_interpretation ->
                   let app =
                     let uu____2444 =
                       let uu____2445 =
                         let uu____2452 =
                           FStar_List.map
                             (FStar_Extraction_ML_Syntax.with_ty
                                FStar_Extraction_ML_Syntax.MLTY_Top)
                             [lid_arg; arity; tac_interpretation] in
                         (h, uu____2452) in
                       FStar_Extraction_ML_Syntax.MLE_App uu____2445 in
                     FStar_All.pipe_left
                       (FStar_Extraction_ML_Syntax.with_ty
                          FStar_Extraction_ML_Syntax.MLTY_Top) uu____2444 in
                   [FStar_Extraction_ML_Syntax.MLM_Top app]
               | FStar_Pervasives_Native.None  -> [] in
             match FStar_Pervasives_Native.snd lbs with
             | hd1::[] ->
                 let uu____2462 =
                   FStar_Syntax_Util.arrow_formals_comp
                     hd1.FStar_Syntax_Syntax.lbtyp in
                 (match uu____2462 with
                  | (bs,comp) ->
                      let t = FStar_Syntax_Util.comp_result comp in
                      let uu____2492 =
                        let uu____2493 = FStar_Syntax_Subst.compress t in
                        uu____2493.FStar_Syntax_Syntax.n in
                      (match uu____2492 with
                       | FStar_Syntax_Syntax.Tm_app (h,args) ->
                           let h1 = FStar_Syntax_Subst.compress h in
                           let tac_lid =
                             let uu____2522 =
                               let uu____2525 =
                                 FStar_Util.right
                                   hd1.FStar_Syntax_Syntax.lbname in
                               uu____2525.FStar_Syntax_Syntax.fv_name in
                             uu____2522.FStar_Syntax_Syntax.v in
                           let assm_lid =
                             let uu____2527 =
                               FStar_All.pipe_left FStar_Ident.id_of_text
                                 (Prims.strcat "__"
                                    (tac_lid.FStar_Ident.ident).FStar_Ident.idText) in
                             FStar_Ident.lid_of_ns_and_id
                               tac_lid.FStar_Ident.ns uu____2527 in
                           let uu____2528 = is_tactic_decl assm_lid h1 in
                           if uu____2528
                           then
                             let uu____2531 =
                               let uu____2532 = FStar_List.hd args in
                               FStar_Pervasives_Native.fst uu____2532 in
                             mk_registration tac_lid assm_lid uu____2531 bs
                           else []
                       | uu____2548 -> []))
             | uu____2549 -> [] in
           let uu____2552 = FStar_Extraction_ML_Term.term_as_mlexpr g elet in
           (match uu____2552 with
            | (ml_let,uu____2566,uu____2567) ->
                (match ml_let.FStar_Extraction_ML_Syntax.expr with
                 | FStar_Extraction_ML_Syntax.MLE_Let
                     ((flavor,uu____2575,bindings),uu____2577) ->
                     let uu____2590 =
                       FStar_List.fold_left2
                         (fun uu____2617  ->
                            fun ml_lb  ->
                              fun uu____2619  ->
                                match (uu____2617, uu____2619) with
                                | ((env,ml_lbs),{
                                                  FStar_Syntax_Syntax.lbname
                                                    = lbname;
                                                  FStar_Syntax_Syntax.lbunivs
                                                    = uu____2641;
                                                  FStar_Syntax_Syntax.lbtyp =
                                                    t;
                                                  FStar_Syntax_Syntax.lbeff =
                                                    uu____2643;
                                                  FStar_Syntax_Syntax.lbdef =
                                                    uu____2644;_})
                                    ->
                                    let lb_lid =
                                      let uu____2666 =
                                        let uu____2669 =
                                          FStar_Util.right lbname in
                                        uu____2669.FStar_Syntax_Syntax.fv_name in
                                      uu____2666.FStar_Syntax_Syntax.v in
                                    let uu____2670 =
                                      let uu____2675 =
                                        FStar_All.pipe_right quals
                                          (FStar_Util.for_some
                                             (fun uu___162_2680  ->
                                                match uu___162_2680 with
                                                | FStar_Syntax_Syntax.Projector
                                                    uu____2681 -> true
                                                | uu____2686 -> false)) in
                                      if uu____2675
                                      then
                                        let mname =
                                          let uu____2692 =
                                            mangle_projector_lid lb_lid in
                                          FStar_All.pipe_right uu____2692
                                            FStar_Extraction_ML_Syntax.mlpath_of_lident in
                                        let uu____2693 =
                                          let uu____2698 =
                                            FStar_Util.right lbname in
                                          let uu____2699 =
                                            FStar_Util.must
                                              ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc in
                                          FStar_Extraction_ML_UEnv.extend_fv'
                                            env uu____2698 mname uu____2699
                                            ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                            false in
                                        match uu____2693 with
                                        | (env1,uu____2705) ->
                                            (env1,
                                              (let uu___167_2707 = ml_lb in
                                               {
                                                 FStar_Extraction_ML_Syntax.mllb_name
                                                   =
                                                   (FStar_Pervasives_Native.snd
                                                      mname);
                                                 FStar_Extraction_ML_Syntax.mllb_tysc
                                                   =
                                                   (uu___167_2707.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                 FStar_Extraction_ML_Syntax.mllb_add_unit
                                                   =
                                                   (uu___167_2707.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                 FStar_Extraction_ML_Syntax.mllb_def
                                                   =
                                                   (uu___167_2707.FStar_Extraction_ML_Syntax.mllb_def);
                                                 FStar_Extraction_ML_Syntax.print_typ
                                                   =
                                                   (uu___167_2707.FStar_Extraction_ML_Syntax.print_typ)
                                               }))
                                      else
                                        (let uu____2711 =
                                           let uu____2712 =
                                             let uu____2717 =
                                               FStar_Util.must
                                                 ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc in
                                             FStar_Extraction_ML_UEnv.extend_lb
                                               env lbname t uu____2717
                                               ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                               false in
                                           FStar_All.pipe_left
                                             FStar_Pervasives_Native.fst
                                             uu____2712 in
                                         (uu____2711, ml_lb)) in
                                    (match uu____2670 with
                                     | (g1,ml_lb1) ->
                                         (g1, (ml_lb1 :: ml_lbs)))) (g, [])
                         bindings (FStar_Pervasives_Native.snd lbs) in
                     (match uu____2590 with
                      | (g1,ml_lbs') ->
                          let flags =
                            FStar_List.choose
                              (fun uu___163_2752  ->
                                 match uu___163_2752 with
                                 | FStar_Syntax_Syntax.Assumption  ->
                                     FStar_Pervasives_Native.Some
                                       FStar_Extraction_ML_Syntax.Assumed
                                 | FStar_Syntax_Syntax.Private  ->
                                     FStar_Pervasives_Native.Some
                                       FStar_Extraction_ML_Syntax.Private
                                 | FStar_Syntax_Syntax.NoExtract  ->
                                     FStar_Pervasives_Native.Some
                                       FStar_Extraction_ML_Syntax.NoExtract
                                 | uu____2755 -> FStar_Pervasives_Native.None)
                              quals in
                          let flags' =
                            FStar_List.choose
                              (fun uu___164_2766  ->
                                 match uu___164_2766 with
                                 | {
                                     FStar_Syntax_Syntax.n =
                                       FStar_Syntax_Syntax.Tm_constant
                                       (FStar_Const.Const_string
                                       (s,uu____2772));
                                     FStar_Syntax_Syntax.pos = uu____2773;
                                     FStar_Syntax_Syntax.vars = uu____2774;_}
                                     ->
                                     FStar_Pervasives_Native.Some
                                       (FStar_Extraction_ML_Syntax.Attribute
                                          s)
                                 | uu____2777 ->
                                     (FStar_Util.print_warning
                                        "Warning: unrecognized, non-string attribute, bother protz for a better error message";
                                      FStar_Pervasives_Native.None)) attrs in
                          let uu____2781 =
                            let uu____2784 =
                              let uu____2787 =
                                let uu____2788 =
                                  FStar_Extraction_ML_Util.mlloc_of_range
                                    se.FStar_Syntax_Syntax.sigrng in
                                FStar_Extraction_ML_Syntax.MLM_Loc uu____2788 in
                              [uu____2787;
                              FStar_Extraction_ML_Syntax.MLM_Let
                                (flavor, (FStar_List.append flags flags'),
                                  (FStar_List.rev ml_lbs'))] in
                            FStar_List.append uu____2784
                              tactic_registration_decl in
                          (g1, uu____2781))
                 | uu____2795 ->
                     let uu____2796 =
                       let uu____2797 =
                         FStar_Extraction_ML_Code.string_of_mlexpr
                           g.FStar_Extraction_ML_UEnv.currentModule ml_let in
                       FStar_Util.format1
                         "Impossible: Translated a let to a non-let: %s"
                         uu____2797 in
                     failwith uu____2796))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____2805,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____2810 =
             FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption) in
           if uu____2810
           then
             let always_fail =
               let imp =
                 let uu____2821 = FStar_Syntax_Util.arrow_formals t in
                 match uu____2821 with
                 | ([],t1) ->
                     let b =
                       let uu____2850 =
                         FStar_Syntax_Syntax.gen_bv "_"
                           FStar_Pervasives_Native.None t1 in
                       FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                         uu____2850 in
                     let uu____2851 = fail_exp lid t1 in
                     FStar_Syntax_Util.abs [b] uu____2851
                       FStar_Pervasives_Native.None
                 | (bs,t1) ->
                     let uu____2870 = fail_exp lid t1 in
                     FStar_Syntax_Util.abs bs uu____2870
                       FStar_Pervasives_Native.None in
               let uu___168_2871 = se in
               let uu____2872 =
                 let uu____2873 =
                   let uu____2880 =
                     let uu____2887 =
                       let uu____2890 =
                         let uu____2891 =
                           let uu____2896 =
                             FStar_Syntax_Syntax.lid_as_fv lid
                               FStar_Syntax_Syntax.Delta_constant
                               FStar_Pervasives_Native.None in
                           FStar_Util.Inr uu____2896 in
                         {
                           FStar_Syntax_Syntax.lbname = uu____2891;
                           FStar_Syntax_Syntax.lbunivs = [];
                           FStar_Syntax_Syntax.lbtyp = t;
                           FStar_Syntax_Syntax.lbeff =
                             FStar_Parser_Const.effect_ML_lid;
                           FStar_Syntax_Syntax.lbdef = imp
                         } in
                       [uu____2890] in
                     (false, uu____2887) in
                   (uu____2880, []) in
                 FStar_Syntax_Syntax.Sig_let uu____2873 in
               {
                 FStar_Syntax_Syntax.sigel = uu____2872;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___168_2871.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___168_2871.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___168_2871.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___168_2871.FStar_Syntax_Syntax.sigattrs)
               } in
             let uu____2907 = extract_sig g always_fail in
             (match uu____2907 with
              | (g1,mlm) ->
                  let uu____2926 =
                    FStar_Util.find_map quals
                      (fun uu___165_2931  ->
                         match uu___165_2931 with
                         | FStar_Syntax_Syntax.Discriminator l ->
                             FStar_Pervasives_Native.Some l
                         | uu____2935 -> FStar_Pervasives_Native.None) in
                  (match uu____2926 with
                   | FStar_Pervasives_Native.Some l ->
                       let uu____2943 =
                         let uu____2946 =
                           let uu____2947 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____2947 in
                         let uu____2948 =
                           let uu____2951 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l in
                           [uu____2951] in
                         uu____2946 :: uu____2948 in
                       (g1, uu____2943)
                   | uu____2954 ->
                       let uu____2957 =
                         FStar_Util.find_map quals
                           (fun uu___166_2963  ->
                              match uu___166_2963 with
                              | FStar_Syntax_Syntax.Projector (l,uu____2967)
                                  -> FStar_Pervasives_Native.Some l
                              | uu____2968 -> FStar_Pervasives_Native.None) in
                       (match uu____2957 with
                        | FStar_Pervasives_Native.Some uu____2975 -> (g1, [])
                        | uu____2978 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____2987 = FStar_Extraction_ML_Term.term_as_mlexpr g e in
           (match uu____2987 with
            | (ml_main,uu____3001,uu____3002) ->
                let uu____3003 =
                  let uu____3006 =
                    let uu____3007 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____3007 in
                  [uu____3006; FStar_Extraction_ML_Syntax.MLM_Top ml_main] in
                (g, uu____3003))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____3010 ->
           failwith "impossible -- removed by tc.fs"
       | FStar_Syntax_Syntax.Sig_assume uu____3017 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____3026 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____3029 -> (g, [])
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (if p = FStar_Syntax_Syntax.LightOff
            then FStar_Options.set_ml_ish ()
            else ();
            (g, [])))
let extract_iface:
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.modul -> env_t =
  fun g  ->
    fun m  ->
      let uu____3057 =
        FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____3057 FStar_Pervasives_Native.fst
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
      (let uu____3102 = FStar_Options.debug_any () in
       if uu____3102
       then
         let uu____3103 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
         FStar_Util.print1 "Extracting module %s\n" uu____3103
       else ());
      (let codegen_opt = FStar_Options.codegen () in
       let uu____3108 = FStar_Options.restore_cmd_line_options true in
       (match codegen_opt with
        | FStar_Pervasives_Native.Some "OCaml" ->
            FStar_Options.set_option "codegen" (FStar_Options.String "OCaml")
        | uu____3110 -> ());
       (let name =
          FStar_Extraction_ML_Syntax.mlpath_of_lident
            m.FStar_Syntax_Syntax.name in
        let g1 =
          let uu___169_3115 = g in
          let uu____3116 =
            FStar_TypeChecker_Env.set_current_module
              g.FStar_Extraction_ML_UEnv.tcenv m.FStar_Syntax_Syntax.name in
          {
            FStar_Extraction_ML_UEnv.tcenv = uu____3116;
            FStar_Extraction_ML_UEnv.gamma =
              (uu___169_3115.FStar_Extraction_ML_UEnv.gamma);
            FStar_Extraction_ML_UEnv.tydefs =
              (uu___169_3115.FStar_Extraction_ML_UEnv.tydefs);
            FStar_Extraction_ML_UEnv.type_names =
              (uu___169_3115.FStar_Extraction_ML_UEnv.type_names);
            FStar_Extraction_ML_UEnv.currentModule = name
          } in
        let uu____3117 =
          FStar_Util.fold_map extract_sig g1
            m.FStar_Syntax_Syntax.declarations in
        match uu____3117 with
        | (g2,sigs) ->
            let mlm = FStar_List.flatten sigs in
            let is_kremlin =
              let uu____3146 = FStar_Options.codegen () in
              match uu____3146 with
              | FStar_Pervasives_Native.Some "Kremlin" -> true
              | uu____3149 -> false in
            let uu____3152 =
              (((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
                 (is_kremlin ||
                    (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)))
                &&
                (FStar_Options.should_extract
                   (m.FStar_Syntax_Syntax.name).FStar_Ident.str) in
            if uu____3152
            then
              ((let uu____3160 =
                  FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
                FStar_Util.print1 "Extracted module %s\n" uu____3160);
               (g2,
                 [FStar_Extraction_ML_Syntax.MLLib
                    [(name, (FStar_Pervasives_Native.Some ([], mlm)),
                       (FStar_Extraction_ML_Syntax.MLLib []))]]))
            else (g2, [])))