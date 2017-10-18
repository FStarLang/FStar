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
  fun uu___185_82  ->
    match uu___185_82 with
    | a::b::[] -> (a, b)
    | uu____87 -> failwith "Expected a list with 2 elements"
let rec extract_meta:
  FStar_Syntax_Syntax.term ->
    FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option
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
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
        FStar_Syntax_Syntax.pos = uu____111;
        FStar_Syntax_Syntax.vars = uu____112;_} when
        let uu____115 =
          let uu____116 = FStar_Syntax_Syntax.lid_of_fv fv in
          FStar_Ident.string_of_lid uu____116 in
        uu____115 = "FStar.Pervasives.CInline" ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CInline
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
        FStar_Syntax_Syntax.pos = uu____118;
        FStar_Syntax_Syntax.vars = uu____119;_} when
        let uu____122 =
          let uu____123 = FStar_Syntax_Syntax.lid_of_fv fv in
          FStar_Ident.string_of_lid uu____123 in
        uu____122 = "FStar.Pervasives.Substitute" ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Substitute
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
        FStar_Syntax_Syntax.pos = uu____125;
        FStar_Syntax_Syntax.vars = uu____126;_} when
        let uu____129 =
          let uu____130 = FStar_Syntax_Syntax.lid_of_fv fv in
          FStar_Ident.string_of_lid uu____130 in
        uu____129 = "FStar.Pervasives.Gc" ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.GCType
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____132;
             FStar_Syntax_Syntax.vars = uu____133;_},({
                                                        FStar_Syntax_Syntax.n
                                                          =
                                                          FStar_Syntax_Syntax.Tm_constant
                                                          (FStar_Const.Const_string
                                                          (s,uu____135));
                                                        FStar_Syntax_Syntax.pos
                                                          = uu____136;
                                                        FStar_Syntax_Syntax.vars
                                                          = uu____137;_},uu____138)::[]);
        FStar_Syntax_Syntax.pos = uu____139;
        FStar_Syntax_Syntax.vars = uu____140;_} when
        let uu____171 =
          let uu____172 = FStar_Syntax_Syntax.lid_of_fv fv in
          FStar_Ident.string_of_lid uu____172 in
        uu____171 = "FStar.Pervasives.PpxDerivingShowConstant" ->
        FStar_Pervasives_Native.Some
          (FStar_Extraction_ML_Syntax.PpxDerivingShowConstant s)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____174;
             FStar_Syntax_Syntax.vars = uu____175;_},({
                                                        FStar_Syntax_Syntax.n
                                                          =
                                                          FStar_Syntax_Syntax.Tm_constant
                                                          (FStar_Const.Const_string
                                                          (s,uu____177));
                                                        FStar_Syntax_Syntax.pos
                                                          = uu____178;
                                                        FStar_Syntax_Syntax.vars
                                                          = uu____179;_},uu____180)::[]);
        FStar_Syntax_Syntax.pos = uu____181;
        FStar_Syntax_Syntax.vars = uu____182;_} when
        let uu____213 =
          let uu____214 = FStar_Syntax_Syntax.lid_of_fv fv in
          FStar_Ident.string_of_lid uu____214 in
        uu____213 = "FStar.Pervasives.Comment" ->
        FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.Comment s)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string (data,uu____216));
        FStar_Syntax_Syntax.pos = uu____217;
        FStar_Syntax_Syntax.vars = uu____218;_} when data = "c_inline" ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CInline
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string (data,uu____222));
        FStar_Syntax_Syntax.pos = uu____223;
        FStar_Syntax_Syntax.vars = uu____224;_} when data = "substitute" ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Substitute
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_meta (x1,uu____228);
        FStar_Syntax_Syntax.pos = uu____229;
        FStar_Syntax_Syntax.vars = uu____230;_} -> extract_meta x1
    | a ->
        ((let uu____239 = FStar_Syntax_Print.term_to_string a in
          FStar_Util.print1_warning
            "Unrecognized attribute (%s), valid attributes are `c_inline`, `substitute`, and `gc`.\n"
            uu____239);
         FStar_Pervasives_Native.None)
let extract_metadata:
  FStar_Syntax_Syntax.term Prims.list ->
    FStar_Extraction_ML_Syntax.meta Prims.list
  = fun metas  -> FStar_List.choose extract_meta metas
let binders_as_mlty_binders:
  'Auu____256 .
    FStar_Extraction_ML_UEnv.env ->
      (FStar_Syntax_Syntax.bv,'Auu____256) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Extraction_ML_UEnv.env,Prims.string Prims.list)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bs  ->
      FStar_Util.fold_map
        (fun env1  ->
           fun uu____294  ->
             match uu____294 with
             | (bv,uu____304) ->
                 let uu____305 =
                   let uu____306 =
                     let uu____309 =
                       let uu____310 =
                         FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv in
                       FStar_Extraction_ML_Syntax.MLTY_Var uu____310 in
                     FStar_Pervasives_Native.Some uu____309 in
                   FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____306 in
                 let uu____311 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv in
                 (uu____305, uu____311)) env bs
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
              let uu____348 =
                let uu____349 = FStar_Syntax_Subst.compress def in
                FStar_All.pipe_right uu____349 FStar_Syntax_Util.unmeta in
              FStar_All.pipe_right uu____348 FStar_Syntax_Util.un_uinst in
            let def2 =
              match def1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_abs uu____351 ->
                  FStar_Extraction_ML_Term.normalize_abs def1
              | uu____368 -> def1 in
            let uu____369 =
              match def2.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____380) ->
                  FStar_Syntax_Subst.open_term bs body
              | uu____401 -> ([], def2) in
            match uu____369 with
            | (bs,body) ->
                let assumed =
                  FStar_Util.for_some
                    (fun uu___186_422  ->
                       match uu___186_422 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____423 -> false) quals in
                let uu____424 = binders_as_mlty_binders env bs in
                (match uu____424 with
                 | (env1,ml_bs) ->
                     let body1 =
                       let uu____444 =
                         FStar_Extraction_ML_Term.term_as_mlty env1 body in
                       FStar_All.pipe_right uu____444
                         (FStar_Extraction_ML_Util.eraseTypeDeep
                            (FStar_Extraction_ML_Util.udelta_unfold env1)) in
                     let mangled_projector =
                       let uu____448 =
                         FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___187_453  ->
                                 match uu___187_453 with
                                 | FStar_Syntax_Syntax.Projector uu____454 ->
                                     true
                                 | uu____459 -> false)) in
                       if uu____448
                       then
                         let mname = mangle_projector_lid lid in
                         FStar_Pervasives_Native.Some
                           ((mname.FStar_Ident.ident).FStar_Ident.idText)
                       else FStar_Pervasives_Native.None in
                     let metadata = extract_metadata attrs in
                     let td =
                       let uu____490 =
                         let uu____511 = lident_as_mlsymbol lid in
                         (assumed, uu____511, mangled_projector, ml_bs,
                           metadata,
                           (FStar_Pervasives_Native.Some
                              (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1))) in
                       [uu____490] in
                     let def3 =
                       let uu____563 =
                         let uu____564 =
                           FStar_Extraction_ML_Util.mlloc_of_range
                             (FStar_Ident.range_of_lid lid) in
                         FStar_Extraction_ML_Syntax.MLM_Loc uu____564 in
                       [uu____563; FStar_Extraction_ML_Syntax.MLM_Ty td] in
                     let env2 =
                       let uu____566 =
                         FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___188_570  ->
                                 match uu___188_570 with
                                 | FStar_Syntax_Syntax.Assumption  -> true
                                 | FStar_Syntax_Syntax.New  -> true
                                 | uu____571 -> false)) in
                       if uu____566
                       then FStar_Extraction_ML_UEnv.extend_type_name env1 fv
                       else FStar_Extraction_ML_UEnv.extend_tydef env1 fv td in
                     (env2, def3))
type data_constructor =
  {
  dname: FStar_Ident.lident;
  dtyp: FStar_Syntax_Syntax.typ;}[@@deriving show]
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
  imetadata: FStar_Extraction_ML_Syntax.metadata;}[@@deriving show]
let __proj__Mkinductive_family__item__iname:
  inductive_family -> FStar_Ident.lident =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; imetadata = __fname__imetadata;_} ->
        __fname__iname
let __proj__Mkinductive_family__item__iparams:
  inductive_family -> FStar_Syntax_Syntax.binders =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; imetadata = __fname__imetadata;_} ->
        __fname__iparams
let __proj__Mkinductive_family__item__ityp:
  inductive_family -> FStar_Syntax_Syntax.term =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; imetadata = __fname__imetadata;_} ->
        __fname__ityp
let __proj__Mkinductive_family__item__idatas:
  inductive_family -> data_constructor Prims.list =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; imetadata = __fname__imetadata;_} ->
        __fname__idatas
let __proj__Mkinductive_family__item__iquals:
  inductive_family -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; imetadata = __fname__imetadata;_} ->
        __fname__iquals
let __proj__Mkinductive_family__item__imetadata:
  inductive_family -> FStar_Extraction_ML_Syntax.metadata =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; imetadata = __fname__imetadata;_} ->
        __fname__imetadata
let print_ifamily: inductive_family -> Prims.unit =
  fun i  ->
    let uu____719 = FStar_Syntax_Print.lid_to_string i.iname in
    let uu____720 = FStar_Syntax_Print.binders_to_string " " i.iparams in
    let uu____721 = FStar_Syntax_Print.term_to_string i.ityp in
    let uu____722 =
      let uu____723 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let uu____734 = FStar_Syntax_Print.lid_to_string d.dname in
                let uu____735 =
                  let uu____736 = FStar_Syntax_Print.term_to_string d.dtyp in
                  Prims.strcat " : " uu____736 in
                Prims.strcat uu____734 uu____735)) in
      FStar_All.pipe_right uu____723 (FStar_String.concat "\n\t\t") in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____719 uu____720 uu____721
      uu____722
let bundle_as_inductive_families:
  'Auu____749 .
    FStar_Extraction_ML_UEnv.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'Auu____749 ->
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
                       let uu____827 = FStar_Syntax_Subst.open_term bs t in
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
                                              t2 in
                                          (match uu____875 with
                                           | (bs',body) ->
                                               let uu____908 =
                                                 FStar_Util.first_N
                                                   (FStar_List.length bs1)
                                                   bs' in
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
                                                                    b in
                                                                   (b',
                                                                    uu____1016) in
                                                                 FStar_Syntax_Syntax.NT
                                                                   uu____1009)
                                                        bs_params bs1 in
                                                    let t3 =
                                                      let uu____1018 =
                                                        let uu____1021 =
                                                          FStar_Syntax_Syntax.mk_Total
                                                            body in
                                                        FStar_Syntax_Util.arrow
                                                          rest uu____1021 in
                                                      FStar_All.pipe_right
                                                        uu____1018
                                                        (FStar_Syntax_Subst.subst
                                                           subst1) in
                                                    [{ dname = d; dtyp = t3 }]))
                                      | uu____1026 -> [])) in
                            let metadata =
                              extract_metadata
                                (FStar_List.append
                                   se.FStar_Syntax_Syntax.sigattrs attrs) in
                            let env2 =
                              let uu____1031 =
                                FStar_Syntax_Syntax.lid_as_fv l
                                  FStar_Syntax_Syntax.Delta_constant
                                  FStar_Pervasives_Native.None in
                              FStar_Extraction_ML_UEnv.extend_type_name env1
                                uu____1031 in
                            (env2,
                              [{
                                 iname = l;
                                 iparams = bs1;
                                 ityp = t1;
                                 idatas = datas1;
                                 iquals = (se.FStar_Syntax_Syntax.sigquals);
                                 imetadata = metadata
                               }]))
                   | uu____1034 -> (env1, [])) env ses in
          match uu____780 with
          | (env1,ifams) -> (env1, (FStar_List.flatten ifams))
type env_t = FStar_Extraction_ML_UEnv.env[@@deriving show]
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
          let uu____1112 =
            FStar_Extraction_ML_Term.term_as_mlty env1 ctor.dtyp in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env1) uu____1112 in
        let steps =
          [FStar_TypeChecker_Normalize.Inlining;
          FStar_TypeChecker_Normalize.UnfoldUntil
            FStar_Syntax_Syntax.Delta_constant;
          FStar_TypeChecker_Normalize.EraseUniverses;
          FStar_TypeChecker_Normalize.AllowUnboundUniverses] in
        let names1 =
          let uu____1119 =
            let uu____1120 =
              let uu____1123 =
                FStar_TypeChecker_Normalize.normalize steps
                  env1.FStar_Extraction_ML_UEnv.tcenv ctor.dtyp in
              FStar_Syntax_Subst.compress uu____1123 in
            uu____1120.FStar_Syntax_Syntax.n in
          match uu____1119 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,uu____1127) ->
              FStar_List.map
                (fun uu____1153  ->
                   match uu____1153 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____1159;
                        FStar_Syntax_Syntax.sort = uu____1160;_},uu____1161)
                       -> ppname.FStar_Ident.idText) bs
          | uu____1164 -> [] in
        let tys = (ml_tyvars, mlt) in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp in
        let uu____1175 =
          let uu____1176 =
            FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false in
          FStar_Pervasives_Native.fst uu____1176 in
        let uu____1181 =
          let uu____1192 = lident_as_mlsymbol ctor.dname in
          let uu____1193 =
            let uu____1200 = FStar_Extraction_ML_Util.argTypes mlt in
            FStar_List.zip names1 uu____1200 in
          (uu____1192, uu____1193) in
        (uu____1175, uu____1181) in
      let extract_one_family env1 ind =
        let uu____1248 = binders_as_mlty_binders env1 ind.iparams in
        match uu____1248 with
        | (env2,vars) ->
            let uu____1283 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor vars) env2) in
            (match uu____1283 with
             | (env3,ctors) ->
                 let uu____1376 = FStar_Syntax_Util.arrow_formals ind.ityp in
                 (match uu____1376 with
                  | (indices,uu____1412) ->
                      let ml_params =
                        let uu____1432 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____1451  ->
                                    let uu____1456 =
                                      FStar_Util.string_of_int i in
                                    Prims.strcat "'dummyV" uu____1456)) in
                        FStar_List.append vars uu____1432 in
                      let tbody =
                        let uu____1458 =
                          FStar_Util.find_opt
                            (fun uu___189_1463  ->
                               match uu___189_1463 with
                               | FStar_Syntax_Syntax.RecordType uu____1464 ->
                                   true
                               | uu____1473 -> false) ind.iquals in
                        match uu____1458 with
                        | FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____1484 = FStar_List.hd ctors in
                            (match uu____1484 with
                             | (uu____1505,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id  ->
                                        fun uu____1544  ->
                                          match uu____1544 with
                                          | (uu____1553,ty) ->
                                              let lid =
                                                FStar_Ident.lid_of_ids
                                                  (FStar_List.append ns [id]) in
                                              let uu____1556 =
                                                lident_as_mlsymbol lid in
                                              (uu____1556, ty)) ids c_ty in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____1557 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors in
                      let uu____1560 =
                        let uu____1579 = lident_as_mlsymbol ind.iname in
                        (false, uu____1579, FStar_Pervasives_Native.None,
                          ml_params, (ind.imetadata),
                          (FStar_Pervasives_Native.Some tbody)) in
                      (env3, uu____1560))) in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____1613,t,uu____1615,uu____1616,uu____1617);
            FStar_Syntax_Syntax.sigrng = uu____1618;
            FStar_Syntax_Syntax.sigquals = uu____1619;
            FStar_Syntax_Syntax.sigmeta = uu____1620;
            FStar_Syntax_Syntax.sigattrs = uu____1621;_}::[],uu____1622),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____1639 = extract_ctor [] env { dname = l; dtyp = t } in
          (match uu____1639 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____1685),quals) ->
          let uu____1699 =
            bundle_as_inductive_families env ses quals
              se.FStar_Syntax_Syntax.sigattrs in
          (match uu____1699 with
           | (env1,ifams) ->
               let uu____1720 =
                 FStar_Util.fold_map extract_one_family env1 ifams in
               (match uu____1720 with
                | (env2,td) -> (env2, [FStar_Extraction_ML_Syntax.MLM_Ty td])))
      | uu____1813 -> failwith "Unexpected signature element"
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
           let uu____1850 = FStar_Syntax_Print.sigelt_to_string se in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____1850);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____1857 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____1866 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____1883 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
           ->
           let extend_env g1 lid ml_name tm tysc =
             let uu____1921 =
               let uu____1926 =
                 FStar_Syntax_Syntax.lid_as_fv lid
                   FStar_Syntax_Syntax.Delta_equational
                   FStar_Pervasives_Native.None in
               FStar_Extraction_ML_UEnv.extend_fv' g1 uu____1926 ml_name tysc
                 false false in
             match uu____1921 with
             | (g2,mangled_name) ->
                 ((let uu____1934 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          g2.FStar_Extraction_ML_UEnv.tcenv)
                       (FStar_Options.Other "ExtractionReify") in
                   if uu____1934
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
             (let uu____1950 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify") in
              if uu____1950
              then
                let uu____1951 = FStar_Syntax_Print.term_to_string tm in
                FStar_Util.print1 "extract_fv term: %s\n" uu____1951
              else ());
             (let uu____1953 =
                let uu____1954 = FStar_Syntax_Subst.compress tm in
                uu____1954.FStar_Syntax_Syntax.n in
              match uu____1953 with
              | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____1962) ->
                  extract_fv tm1
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let mlp =
                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  let uu____1969 =
                    let uu____1978 = FStar_Extraction_ML_UEnv.lookup_fv g fv in
                    FStar_All.pipe_left FStar_Util.right uu____1978 in
                  (match uu____1969 with
                   | (uu____2035,uu____2036,tysc,uu____2038) ->
                       let uu____2039 =
                         FStar_All.pipe_left
                           (FStar_Extraction_ML_Syntax.with_ty
                              FStar_Extraction_ML_Syntax.MLTY_Top)
                           (FStar_Extraction_ML_Syntax.MLE_Name mlp) in
                       (uu____2039, tysc))
              | uu____2040 -> failwith "Not an fv") in
           let extract_action g1 a =
             (let uu____2066 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g1.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify") in
              if uu____2066
              then
                let uu____2067 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_typ in
                let uu____2068 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_defn in
                FStar_Util.print2 "Action type %s and term %s\n" uu____2067
                  uu____2068
              else ());
             (let uu____2070 = FStar_Extraction_ML_UEnv.action_name ed a in
              match uu____2070 with
              | (a_nm,a_lid) ->
                  let lbname =
                    let uu____2086 =
                      FStar_Syntax_Syntax.new_bv
                        (FStar_Pervasives_Native.Some
                           ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                        FStar_Syntax_Syntax.tun in
                    FStar_Util.Inl uu____2086 in
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
                  let uu____2112 =
                    FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb in
                  (match uu____2112 with
                   | (a_let,uu____2124,ty) ->
                       ((let uu____2127 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug
                                g1.FStar_Extraction_ML_UEnv.tcenv)
                             (FStar_Options.Other "ExtractionReify") in
                         if uu____2127
                         then
                           let uu____2128 =
                             FStar_Extraction_ML_Code.string_of_mlexpr a_nm
                               a_let in
                           FStar_Util.print1 "Extracted action term: %s\n"
                             uu____2128
                         else ());
                        (let uu____2130 =
                           match a_let.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_Let
                               ((uu____2139,uu____2140,mllb::[]),uu____2142)
                               ->
                               (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                                with
                                | FStar_Pervasives_Native.Some tysc ->
                                    ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                      tysc)
                                | FStar_Pervasives_Native.None  ->
                                    failwith "No type scheme")
                           | uu____2162 -> failwith "Impossible" in
                         match uu____2130 with
                         | (exp,tysc) ->
                             ((let uu____2174 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug
                                      g1.FStar_Extraction_ML_UEnv.tcenv)
                                   (FStar_Options.Other "ExtractionReify") in
                               if uu____2174
                               then
                                 ((let uu____2176 =
                                     FStar_Extraction_ML_Code.string_of_mlty
                                       a_nm
                                       (FStar_Pervasives_Native.snd tysc) in
                                   FStar_Util.print1
                                     "Extracted action type: %s\n" uu____2176);
                                  FStar_List.iter
                                    (fun x  ->
                                       FStar_Util.print1 "and binders: %s\n"
                                         x)
                                    (FStar_Pervasives_Native.fst tysc))
                               else ());
                              extend_env g1 a_lid a_nm exp tysc))))) in
           let uu____2180 =
             let uu____2185 =
               extract_fv
                 (FStar_Pervasives_Native.snd
                    ed.FStar_Syntax_Syntax.return_repr) in
             match uu____2185 with
             | (return_tm,ty_sc) ->
                 let uu____2198 =
                   FStar_Extraction_ML_UEnv.monad_op_name ed "return" in
                 (match uu____2198 with
                  | (return_nm,return_lid) ->
                      extend_env g return_lid return_nm return_tm ty_sc) in
           (match uu____2180 with
            | (g1,return_decl) ->
                let uu____2217 =
                  let uu____2222 =
                    extract_fv
                      (FStar_Pervasives_Native.snd
                         ed.FStar_Syntax_Syntax.bind_repr) in
                  match uu____2222 with
                  | (bind_tm,ty_sc) ->
                      let uu____2235 =
                        FStar_Extraction_ML_UEnv.monad_op_name ed "bind" in
                      (match uu____2235 with
                       | (bind_nm,bind_lid) ->
                           extend_env g1 bind_lid bind_nm bind_tm ty_sc) in
                (match uu____2217 with
                 | (g2,bind_decl) ->
                     let uu____2254 =
                       FStar_Util.fold_map extract_action g2
                         ed.FStar_Syntax_Syntax.actions in
                     (match uu____2254 with
                      | (g3,actions) ->
                          (g3,
                            (FStar_List.append [return_decl; bind_decl]
                               actions)))))
       | FStar_Syntax_Syntax.Sig_new_effect uu____2275 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____2279,t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let attrs = se.FStar_Syntax_Syntax.sigattrs in
           let uu____2287 =
             let uu____2288 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___190_2292  ->
                       match uu___190_2292 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____2293 -> false)) in
             Prims.op_Negation uu____2288 in
           if uu____2287
           then (g, [])
           else
             (let uu____2303 = FStar_Syntax_Util.arrow_formals t in
              match uu____2303 with
              | (bs,uu____2323) ->
                  let fv =
                    FStar_Syntax_Syntax.lid_as_fv lid
                      FStar_Syntax_Syntax.Delta_constant
                      FStar_Pervasives_Native.None in
                  let uu____2341 =
                    FStar_Syntax_Util.abs bs FStar_Syntax_Syntax.t_unit
                      FStar_Pervasives_Native.None in
                  extract_typ_abbrev g fv quals attrs uu____2341)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____2343) when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____2359 =
             let uu____2368 =
               FStar_TypeChecker_Env.open_universes_in
                 g.FStar_Extraction_ML_UEnv.tcenv
                 lb.FStar_Syntax_Syntax.lbunivs
                 [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp] in
             match uu____2368 with
             | (tcenv,uu____2392,def_typ) ->
                 let uu____2398 = as_pair def_typ in (tcenv, uu____2398) in
           (match uu____2359 with
            | (tcenv,(lbdef,lbtyp)) ->
                let lbtyp1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.UnfoldUntil
                      FStar_Syntax_Syntax.Delta_constant] tcenv lbtyp in
                let lbdef1 =
                  FStar_TypeChecker_Normalize.eta_expand_with_type tcenv
                    lbdef lbtyp1 in
                let uu____2422 =
                  FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                extract_typ_abbrev g uu____2422 quals
                  se.FStar_Syntax_Syntax.sigattrs lbdef1)
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____2424) ->
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
               | FStar_Syntax_Syntax.Tm_uinst (h',uu____2451) ->
                   let uu____2456 =
                     let uu____2457 = FStar_Syntax_Subst.compress h' in
                     uu____2457.FStar_Syntax_Syntax.n in
                   (match uu____2456 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.tactic_lid
                        ->
                        let uu____2461 =
                          let uu____2462 =
                            FStar_Extraction_ML_Syntax.string_of_mlpath
                              g.FStar_Extraction_ML_UEnv.currentModule in
                          FStar_Util.starts_with uu____2462 "FStar.Tactics" in
                        Prims.op_Negation uu____2461
                    | uu____2463 -> false)
               | uu____2464 -> false in
             let mk_registration tac_lid assm_lid t bs =
               let h =
                 let uu____2493 =
                   let uu____2494 =
                     let uu____2495 =
                       FStar_Ident.lid_of_str
                         "FStar_Tactics_Native.register_tactic" in
                     FStar_Extraction_ML_Syntax.mlpath_of_lident uu____2495 in
                   FStar_Extraction_ML_Syntax.MLE_Name uu____2494 in
                 FStar_All.pipe_left
                   (FStar_Extraction_ML_Syntax.with_ty
                      FStar_Extraction_ML_Syntax.MLTY_Top) uu____2493 in
               let lid_arg =
                 let uu____2497 =
                   let uu____2498 = FStar_Ident.string_of_lid assm_lid in
                   FStar_Extraction_ML_Syntax.MLC_String uu____2498 in
                 FStar_Extraction_ML_Syntax.MLE_Const uu____2497 in
               let tac_arity = FStar_List.length bs in
               let arity =
                 let uu____2505 =
                   let uu____2506 =
                     let uu____2507 =
                       FStar_Util.string_of_int
                         (tac_arity + (Prims.parse_int "1")) in
                     FStar_Ident.lid_of_str uu____2507 in
                   FStar_Extraction_ML_Syntax.mlpath_of_lident uu____2506 in
                 FStar_Extraction_ML_Syntax.MLE_Name uu____2505 in
               let uu____2514 =
                 FStar_Extraction_ML_Util.mk_interpretation_fun tac_lid
                   lid_arg t bs in
               match uu____2514 with
               | FStar_Pervasives_Native.Some tac_interpretation ->
                   let app =
                     let uu____2521 =
                       let uu____2522 =
                         let uu____2529 =
                           FStar_List.map
                             (FStar_Extraction_ML_Syntax.with_ty
                                FStar_Extraction_ML_Syntax.MLTY_Top)
                             [lid_arg; arity; tac_interpretation] in
                         (h, uu____2529) in
                       FStar_Extraction_ML_Syntax.MLE_App uu____2522 in
                     FStar_All.pipe_left
                       (FStar_Extraction_ML_Syntax.with_ty
                          FStar_Extraction_ML_Syntax.MLTY_Top) uu____2521 in
                   [FStar_Extraction_ML_Syntax.MLM_Top app]
               | FStar_Pervasives_Native.None  -> [] in
             match FStar_Pervasives_Native.snd lbs with
             | hd1::[] ->
                 let uu____2539 =
                   FStar_Syntax_Util.arrow_formals_comp
                     hd1.FStar_Syntax_Syntax.lbtyp in
                 (match uu____2539 with
                  | (bs,comp) ->
                      let t = FStar_Syntax_Util.comp_result comp in
                      let uu____2569 =
                        let uu____2570 = FStar_Syntax_Subst.compress t in
                        uu____2570.FStar_Syntax_Syntax.n in
                      (match uu____2569 with
                       | FStar_Syntax_Syntax.Tm_app (h,args) ->
                           let h1 = FStar_Syntax_Subst.compress h in
                           let tac_lid =
                             let uu____2599 =
                               let uu____2602 =
                                 FStar_Util.right
                                   hd1.FStar_Syntax_Syntax.lbname in
                               uu____2602.FStar_Syntax_Syntax.fv_name in
                             uu____2599.FStar_Syntax_Syntax.v in
                           let assm_lid =
                             let uu____2604 =
                               FStar_All.pipe_left FStar_Ident.id_of_text
                                 (Prims.strcat "__"
                                    (tac_lid.FStar_Ident.ident).FStar_Ident.idText) in
                             FStar_Ident.lid_of_ns_and_id
                               tac_lid.FStar_Ident.ns uu____2604 in
                           let uu____2605 = is_tactic_decl assm_lid h1 in
                           if uu____2605
                           then
                             let uu____2608 =
                               let uu____2609 = FStar_List.hd args in
                               FStar_Pervasives_Native.fst uu____2609 in
                             mk_registration tac_lid assm_lid uu____2608 bs
                           else []
                       | uu____2625 -> []))
             | uu____2626 -> [] in
           let uu____2629 = FStar_Extraction_ML_Term.term_as_mlexpr g elet in
           (match uu____2629 with
            | (ml_let,uu____2643,uu____2644) ->
                (match ml_let.FStar_Extraction_ML_Syntax.expr with
                 | FStar_Extraction_ML_Syntax.MLE_Let
                     ((flavor,uu____2652,bindings),uu____2654) ->
                     let uu____2667 =
                       FStar_List.fold_left2
                         (fun uu____2694  ->
                            fun ml_lb  ->
                              fun uu____2696  ->
                                match (uu____2694, uu____2696) with
                                | ((env,ml_lbs),{
                                                  FStar_Syntax_Syntax.lbname
                                                    = lbname;
                                                  FStar_Syntax_Syntax.lbunivs
                                                    = uu____2718;
                                                  FStar_Syntax_Syntax.lbtyp =
                                                    t;
                                                  FStar_Syntax_Syntax.lbeff =
                                                    uu____2720;
                                                  FStar_Syntax_Syntax.lbdef =
                                                    uu____2721;_})
                                    ->
                                    let lb_lid =
                                      let uu____2743 =
                                        let uu____2746 =
                                          FStar_Util.right lbname in
                                        uu____2746.FStar_Syntax_Syntax.fv_name in
                                      uu____2743.FStar_Syntax_Syntax.v in
                                    let uu____2747 =
                                      let uu____2752 =
                                        FStar_All.pipe_right quals
                                          (FStar_Util.for_some
                                             (fun uu___191_2757  ->
                                                match uu___191_2757 with
                                                | FStar_Syntax_Syntax.Projector
                                                    uu____2758 -> true
                                                | uu____2763 -> false)) in
                                      if uu____2752
                                      then
                                        let mname =
                                          let uu____2769 =
                                            mangle_projector_lid lb_lid in
                                          FStar_All.pipe_right uu____2769
                                            FStar_Extraction_ML_Syntax.mlpath_of_lident in
                                        let uu____2770 =
                                          let uu____2775 =
                                            FStar_Util.right lbname in
                                          let uu____2776 =
                                            FStar_Util.must
                                              ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc in
                                          FStar_Extraction_ML_UEnv.extend_fv'
                                            env uu____2775 mname uu____2776
                                            ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                            false in
                                        match uu____2770 with
                                        | (env1,uu____2782) ->
                                            (env1,
                                              (let uu___195_2784 = ml_lb in
                                               {
                                                 FStar_Extraction_ML_Syntax.mllb_name
                                                   =
                                                   (FStar_Pervasives_Native.snd
                                                      mname);
                                                 FStar_Extraction_ML_Syntax.mllb_tysc
                                                   =
                                                   (uu___195_2784.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                 FStar_Extraction_ML_Syntax.mllb_add_unit
                                                   =
                                                   (uu___195_2784.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                 FStar_Extraction_ML_Syntax.mllb_def
                                                   =
                                                   (uu___195_2784.FStar_Extraction_ML_Syntax.mllb_def);
                                                 FStar_Extraction_ML_Syntax.print_typ
                                                   =
                                                   (uu___195_2784.FStar_Extraction_ML_Syntax.print_typ)
                                               }))
                                      else
                                        (let uu____2788 =
                                           let uu____2789 =
                                             let uu____2794 =
                                               FStar_Util.must
                                                 ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc in
                                             FStar_Extraction_ML_UEnv.extend_lb
                                               env lbname t uu____2794
                                               ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                               false in
                                           FStar_All.pipe_left
                                             FStar_Pervasives_Native.fst
                                             uu____2789 in
                                         (uu____2788, ml_lb)) in
                                    (match uu____2747 with
                                     | (g1,ml_lb1) ->
                                         (g1, (ml_lb1 :: ml_lbs)))) (g, [])
                         bindings (FStar_Pervasives_Native.snd lbs) in
                     (match uu____2667 with
                      | (g1,ml_lbs') ->
                          let flags =
                            FStar_List.choose
                              (fun uu___192_2829  ->
                                 match uu___192_2829 with
                                 | FStar_Syntax_Syntax.Assumption  ->
                                     FStar_Pervasives_Native.Some
                                       FStar_Extraction_ML_Syntax.Assumed
                                 | FStar_Syntax_Syntax.Private  ->
                                     FStar_Pervasives_Native.Some
                                       FStar_Extraction_ML_Syntax.Private
                                 | FStar_Syntax_Syntax.NoExtract  ->
                                     FStar_Pervasives_Native.Some
                                       FStar_Extraction_ML_Syntax.NoExtract
                                 | uu____2832 -> FStar_Pervasives_Native.None)
                              quals in
                          let flags' = extract_metadata attrs in
                          let uu____2836 =
                            let uu____2839 =
                              let uu____2842 =
                                let uu____2843 =
                                  FStar_Extraction_ML_Util.mlloc_of_range
                                    se.FStar_Syntax_Syntax.sigrng in
                                FStar_Extraction_ML_Syntax.MLM_Loc uu____2843 in
                              [uu____2842;
                              FStar_Extraction_ML_Syntax.MLM_Let
                                (flavor, (FStar_List.append flags flags'),
                                  (FStar_List.rev ml_lbs'))] in
                            FStar_List.append uu____2839
                              tactic_registration_decl in
                          (g1, uu____2836))
                 | uu____2850 ->
                     let uu____2851 =
                       let uu____2852 =
                         FStar_Extraction_ML_Code.string_of_mlexpr
                           g.FStar_Extraction_ML_UEnv.currentModule ml_let in
                       FStar_Util.format1
                         "Impossible: Translated a let to a non-let: %s"
                         uu____2852 in
                     failwith uu____2851))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____2860,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____2865 =
             FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption) in
           if uu____2865
           then
             let always_fail =
               let imp =
                 let uu____2876 = FStar_Syntax_Util.arrow_formals t in
                 match uu____2876 with
                 | ([],t1) ->
                     let b =
                       let uu____2905 =
                         FStar_Syntax_Syntax.gen_bv "_"
                           FStar_Pervasives_Native.None t1 in
                       FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                         uu____2905 in
                     let uu____2906 = fail_exp lid t1 in
                     FStar_Syntax_Util.abs [b] uu____2906
                       FStar_Pervasives_Native.None
                 | (bs,t1) ->
                     let uu____2925 = fail_exp lid t1 in
                     FStar_Syntax_Util.abs bs uu____2925
                       FStar_Pervasives_Native.None in
               let uu___196_2926 = se in
               let uu____2927 =
                 let uu____2928 =
                   let uu____2935 =
                     let uu____2942 =
                       let uu____2945 =
                         let uu____2946 =
                           let uu____2951 =
                             FStar_Syntax_Syntax.lid_as_fv lid
                               FStar_Syntax_Syntax.Delta_constant
                               FStar_Pervasives_Native.None in
                           FStar_Util.Inr uu____2951 in
                         {
                           FStar_Syntax_Syntax.lbname = uu____2946;
                           FStar_Syntax_Syntax.lbunivs = [];
                           FStar_Syntax_Syntax.lbtyp = t;
                           FStar_Syntax_Syntax.lbeff =
                             FStar_Parser_Const.effect_ML_lid;
                           FStar_Syntax_Syntax.lbdef = imp
                         } in
                       [uu____2945] in
                     (false, uu____2942) in
                   (uu____2935, []) in
                 FStar_Syntax_Syntax.Sig_let uu____2928 in
               {
                 FStar_Syntax_Syntax.sigel = uu____2927;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___196_2926.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___196_2926.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___196_2926.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___196_2926.FStar_Syntax_Syntax.sigattrs)
               } in
             let uu____2962 = extract_sig g always_fail in
             (match uu____2962 with
              | (g1,mlm) ->
                  let uu____2981 =
                    FStar_Util.find_map quals
                      (fun uu___193_2986  ->
                         match uu___193_2986 with
                         | FStar_Syntax_Syntax.Discriminator l ->
                             FStar_Pervasives_Native.Some l
                         | uu____2990 -> FStar_Pervasives_Native.None) in
                  (match uu____2981 with
                   | FStar_Pervasives_Native.Some l ->
                       let uu____2998 =
                         let uu____3001 =
                           let uu____3002 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____3002 in
                         let uu____3003 =
                           let uu____3006 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l in
                           [uu____3006] in
                         uu____3001 :: uu____3003 in
                       (g1, uu____2998)
                   | uu____3009 ->
                       let uu____3012 =
                         FStar_Util.find_map quals
                           (fun uu___194_3018  ->
                              match uu___194_3018 with
                              | FStar_Syntax_Syntax.Projector (l,uu____3022)
                                  -> FStar_Pervasives_Native.Some l
                              | uu____3023 -> FStar_Pervasives_Native.None) in
                       (match uu____3012 with
                        | FStar_Pervasives_Native.Some uu____3030 -> (g1, [])
                        | uu____3033 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____3042 = FStar_Extraction_ML_Term.term_as_mlexpr g e in
           (match uu____3042 with
            | (ml_main,uu____3056,uu____3057) ->
                let uu____3058 =
                  let uu____3061 =
                    let uu____3062 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____3062 in
                  [uu____3061; FStar_Extraction_ML_Syntax.MLM_Top ml_main] in
                (g, uu____3058))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____3065 ->
           failwith "impossible -- removed by tc.fs"
       | FStar_Syntax_Syntax.Sig_assume uu____3072 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____3081 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____3084 -> (g, [])
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (if p = FStar_Syntax_Syntax.LightOff
            then FStar_Options.set_ml_ish ()
            else ();
            (g, [])))
let extract_iface:
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.modul -> env_t =
  fun g  ->
    fun m  ->
      let uu____3112 =
        FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____3112 FStar_Pervasives_Native.fst
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
      (let uu____3157 = FStar_Options.debug_any () in
       if uu____3157
       then
         let uu____3158 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
         FStar_Util.print1 "Extracting module %s\n" uu____3158
       else ());
      (let codegen_opt = FStar_Options.codegen () in
       let uu____3163 = FStar_Options.restore_cmd_line_options true in
       (match codegen_opt with
        | FStar_Pervasives_Native.Some "OCaml" ->
            FStar_Options.set_option "codegen" (FStar_Options.String "OCaml")
        | uu____3165 -> ());
       (let name =
          FStar_Extraction_ML_Syntax.mlpath_of_lident
            m.FStar_Syntax_Syntax.name in
        let g1 =
          let uu___197_3170 = g in
          let uu____3171 =
            FStar_TypeChecker_Env.set_current_module
              g.FStar_Extraction_ML_UEnv.tcenv m.FStar_Syntax_Syntax.name in
          {
            FStar_Extraction_ML_UEnv.tcenv = uu____3171;
            FStar_Extraction_ML_UEnv.gamma =
              (uu___197_3170.FStar_Extraction_ML_UEnv.gamma);
            FStar_Extraction_ML_UEnv.tydefs =
              (uu___197_3170.FStar_Extraction_ML_UEnv.tydefs);
            FStar_Extraction_ML_UEnv.type_names =
              (uu___197_3170.FStar_Extraction_ML_UEnv.type_names);
            FStar_Extraction_ML_UEnv.currentModule = name
          } in
        let uu____3172 =
          FStar_Util.fold_map extract_sig g1
            m.FStar_Syntax_Syntax.declarations in
        match uu____3172 with
        | (g2,sigs) ->
            let mlm = FStar_List.flatten sigs in
            let is_kremlin =
              let uu____3201 = FStar_Options.codegen () in
              match uu____3201 with
              | FStar_Pervasives_Native.Some "Kremlin" -> true
              | uu____3204 -> false in
            let uu____3207 =
              (((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
                 (is_kremlin ||
                    (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)))
                &&
                (FStar_Options.should_extract
                   (m.FStar_Syntax_Syntax.name).FStar_Ident.str) in
            if uu____3207
            then
              ((let uu____3215 =
                  FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
                FStar_Util.print1 "Extracted module %s\n" uu____3215);
               (g2,
                 [FStar_Extraction_ML_Syntax.MLLib
                    [(name, (FStar_Pervasives_Native.Some ([], mlm)),
                       (FStar_Extraction_ML_Syntax.MLLib []))]]))
            else (g2, [])))