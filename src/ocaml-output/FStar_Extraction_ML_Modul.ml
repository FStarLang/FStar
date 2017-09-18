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
  fun uu___154_82  ->
    match uu___154_82 with
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
            "Warning: unrecognized attribute (%s), valid attributes are `c_inline`, `substitute`, and `gc`."
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
        (FStar_Extraction_ML_UEnv.env,(Prims.string,Prims.int)
                                        FStar_Pervasives_Native.tuple2
                                        Prims.list)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bs  ->
      FStar_Util.fold_map
        (fun env1  ->
           fun uu____302  ->
             match uu____302 with
             | (bv,uu____316) ->
                 let uu____317 =
                   let uu____318 =
                     let uu____321 =
                       let uu____322 =
                         FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv in
                       FStar_Extraction_ML_Syntax.MLTY_Var uu____322 in
                     FStar_Pervasives_Native.Some uu____321 in
                   FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____318 in
                 let uu____323 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv in
                 (uu____317, uu____323)) env bs
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
              let uu____368 =
                let uu____369 = FStar_Syntax_Subst.compress def in
                FStar_All.pipe_right uu____369 FStar_Syntax_Util.unmeta in
              FStar_All.pipe_right uu____368 FStar_Syntax_Util.un_uinst in
            let def2 =
              match def1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_abs uu____371 ->
                  FStar_Extraction_ML_Term.normalize_abs def1
              | uu____388 -> def1 in
            let uu____389 =
              match def2.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____400) ->
                  FStar_Syntax_Subst.open_term bs body
              | uu____421 -> ([], def2) in
            match uu____389 with
            | (bs,body) ->
                let assumed =
                  FStar_Util.for_some
                    (fun uu___155_442  ->
                       match uu___155_442 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____443 -> false) quals in
                let uu____444 = binders_as_mlty_binders env bs in
                (match uu____444 with
                 | (env1,ml_bs) ->
                     let body1 =
                       let uu____476 =
                         FStar_Extraction_ML_Term.term_as_mlty env1 body in
                       FStar_All.pipe_right uu____476
                         (FStar_Extraction_ML_Util.eraseTypeDeep
                            (FStar_Extraction_ML_Util.udelta_unfold env1)) in
                     let mangled_projector =
                       let uu____480 =
                         FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___156_485  ->
                                 match uu___156_485 with
                                 | FStar_Syntax_Syntax.Projector uu____486 ->
                                     true
                                 | uu____491 -> false)) in
                       if uu____480
                       then
                         let mname = mangle_projector_lid lid in
                         FStar_Pervasives_Native.Some
                           ((mname.FStar_Ident.ident).FStar_Ident.idText)
                       else FStar_Pervasives_Native.None in
                     let metadata = extract_metadata attrs in
                     let td =
                       let uu____526 =
                         let uu____551 = lident_as_mlsymbol lid in
                         (assumed, uu____551, mangled_projector, ml_bs,
                           metadata,
                           (FStar_Pervasives_Native.Some
                              (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1))) in
                       [uu____526] in
                     let def3 =
                       let uu____615 =
                         let uu____616 =
                           FStar_Extraction_ML_Util.mlloc_of_range
                             (FStar_Ident.range_of_lid lid) in
                         FStar_Extraction_ML_Syntax.MLM_Loc uu____616 in
                       [uu____615; FStar_Extraction_ML_Syntax.MLM_Ty td] in
                     let env2 =
                       let uu____618 =
                         FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___157_622  ->
                                 match uu___157_622 with
                                 | FStar_Syntax_Syntax.Assumption  -> true
                                 | FStar_Syntax_Syntax.New  -> true
                                 | uu____623 -> false)) in
                       if uu____618
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
    let uu____771 = FStar_Syntax_Print.lid_to_string i.iname in
    let uu____772 = FStar_Syntax_Print.binders_to_string " " i.iparams in
    let uu____773 = FStar_Syntax_Print.term_to_string i.ityp in
    let uu____774 =
      let uu____775 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let uu____786 = FStar_Syntax_Print.lid_to_string d.dname in
                let uu____787 =
                  let uu____788 = FStar_Syntax_Print.term_to_string d.dtyp in
                  Prims.strcat " : " uu____788 in
                Prims.strcat uu____786 uu____787)) in
      FStar_All.pipe_right uu____775 (FStar_String.concat "\n\t\t") in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____771 uu____772 uu____773
      uu____774
let bundle_as_inductive_families:
  'Auu____801 .
    FStar_Extraction_ML_UEnv.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'Auu____801 ->
          FStar_Syntax_Syntax.attribute Prims.list ->
            (FStar_Extraction_ML_UEnv.env,inductive_family Prims.list)
              FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun attrs  ->
          let uu____832 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun se  ->
                   match se.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,_us,bs,t,_mut_i,datas) ->
                       let uu____879 = FStar_Syntax_Subst.open_term bs t in
                       (match uu____879 with
                        | (bs1,t1) ->
                            let datas1 =
                              FStar_All.pipe_right ses
                                (FStar_List.collect
                                   (fun se1  ->
                                      match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_datacon
                                          (d,uu____918,t2,l',nparams,uu____922)
                                          when FStar_Ident.lid_equals l l' ->
                                          let uu____927 =
                                            FStar_Syntax_Util.arrow_formals
                                              t2 in
                                          (match uu____927 with
                                           | (bs',body) ->
                                               let uu____960 =
                                                 FStar_Util.first_N
                                                   (FStar_List.length bs1)
                                                   bs' in
                                               (match uu____960 with
                                                | (bs_params,rest) ->
                                                    let subst1 =
                                                      FStar_List.map2
                                                        (fun uu____1031  ->
                                                           fun uu____1032  ->
                                                             match (uu____1031,
                                                                    uu____1032)
                                                             with
                                                             | ((b',uu____1050),
                                                                (b,uu____1052))
                                                                 ->
                                                                 let uu____1061
                                                                   =
                                                                   let uu____1068
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b in
                                                                   (b',
                                                                    uu____1068) in
                                                                 FStar_Syntax_Syntax.NT
                                                                   uu____1061)
                                                        bs_params bs1 in
                                                    let t3 =
                                                      let uu____1070 =
                                                        let uu____1073 =
                                                          FStar_Syntax_Syntax.mk_Total
                                                            body in
                                                        FStar_Syntax_Util.arrow
                                                          rest uu____1073 in
                                                      FStar_All.pipe_right
                                                        uu____1070
                                                        (FStar_Syntax_Subst.subst
                                                           subst1) in
                                                    [{ dname = d; dtyp = t3 }]))
                                      | uu____1078 -> [])) in
                            let metadata =
                              extract_metadata
                                (FStar_List.append
                                   se.FStar_Syntax_Syntax.sigattrs attrs) in
                            let env2 =
                              let uu____1083 =
                                FStar_Syntax_Syntax.lid_as_fv l
                                  FStar_Syntax_Syntax.Delta_constant
                                  FStar_Pervasives_Native.None in
                              FStar_Extraction_ML_UEnv.extend_type_name env1
                                uu____1083 in
                            (env2,
                              [{
                                 iname = l;
                                 iparams = bs1;
                                 ityp = t1;
                                 idatas = datas1;
                                 iquals = (se.FStar_Syntax_Syntax.sigquals);
                                 imetadata = metadata
                               }]))
                   | uu____1086 -> (env1, [])) env ses in
          match uu____832 with
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
          let uu____1172 =
            FStar_Extraction_ML_Term.term_as_mlty env1 ctor.dtyp in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env1) uu____1172 in
        let steps =
          [FStar_TypeChecker_Normalize.Inlining;
          FStar_TypeChecker_Normalize.UnfoldUntil
            FStar_Syntax_Syntax.Delta_constant;
          FStar_TypeChecker_Normalize.EraseUniverses;
          FStar_TypeChecker_Normalize.AllowUnboundUniverses] in
        let names1 =
          let uu____1179 =
            let uu____1180 =
              let uu____1183 =
                FStar_TypeChecker_Normalize.normalize steps
                  env1.FStar_Extraction_ML_UEnv.tcenv ctor.dtyp in
              FStar_Syntax_Subst.compress uu____1183 in
            uu____1180.FStar_Syntax_Syntax.n in
          match uu____1179 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,uu____1187) ->
              FStar_List.map
                (fun uu____1213  ->
                   match uu____1213 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____1219;
                        FStar_Syntax_Syntax.sort = uu____1220;_},uu____1221)
                       -> ppname.FStar_Ident.idText) bs
          | uu____1224 -> [] in
        let tys = (ml_tyvars, mlt) in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp in
        let uu____1243 =
          let uu____1244 =
            FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false in
          FStar_Pervasives_Native.fst uu____1244 in
        let uu____1249 =
          let uu____1260 = lident_as_mlsymbol ctor.dname in
          let uu____1261 =
            let uu____1268 = FStar_Extraction_ML_Util.argTypes mlt in
            FStar_List.zip names1 uu____1268 in
          (uu____1260, uu____1261) in
        (uu____1243, uu____1249) in
      let extract_one_family env1 ind =
        let uu____1320 = binders_as_mlty_binders env1 ind.iparams in
        match uu____1320 with
        | (env2,vars) ->
            let uu____1371 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor vars) env2) in
            (match uu____1371 with
             | (env3,ctors) ->
                 let uu____1468 = FStar_Syntax_Util.arrow_formals ind.ityp in
                 (match uu____1468 with
                  | (indices,uu____1508) ->
                      let ml_params =
                        let uu____1532 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____1563  ->
                                    let uu____1568 =
                                      let uu____1569 =
                                        FStar_Util.string_of_int i in
                                      Prims.strcat "'dummyV" uu____1569 in
                                    (uu____1568, (Prims.parse_int "0")))) in
                        FStar_List.append vars uu____1532 in
                      let tbody =
                        let uu____1575 =
                          FStar_Util.find_opt
                            (fun uu___158_1580  ->
                               match uu___158_1580 with
                               | FStar_Syntax_Syntax.RecordType uu____1581 ->
                                   true
                               | uu____1590 -> false) ind.iquals in
                        match uu____1575 with
                        | FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____1601 = FStar_List.hd ctors in
                            (match uu____1601 with
                             | (uu____1622,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id  ->
                                        fun uu____1661  ->
                                          match uu____1661 with
                                          | (uu____1670,ty) ->
                                              let lid =
                                                FStar_Ident.lid_of_ids
                                                  (FStar_List.append ns [id]) in
                                              let uu____1673 =
                                                lident_as_mlsymbol lid in
                                              (uu____1673, ty)) ids c_ty in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____1674 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors in
                      let uu____1677 =
                        let uu____1700 = lident_as_mlsymbol ind.iname in
                        (false, uu____1700, FStar_Pervasives_Native.None,
                          ml_params, (ind.imetadata),
                          (FStar_Pervasives_Native.Some tbody)) in
                      (env3, uu____1677))) in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____1742,t,uu____1744,uu____1745,uu____1746);
            FStar_Syntax_Syntax.sigrng = uu____1747;
            FStar_Syntax_Syntax.sigquals = uu____1748;
            FStar_Syntax_Syntax.sigmeta = uu____1749;
            FStar_Syntax_Syntax.sigattrs = uu____1750;_}::[],uu____1751),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____1768 = extract_ctor [] env { dname = l; dtyp = t } in
          (match uu____1768 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____1818),quals) ->
          let uu____1832 =
            bundle_as_inductive_families env ses quals
              se.FStar_Syntax_Syntax.sigattrs in
          (match uu____1832 with
           | (env1,ifams) ->
               let uu____1853 =
                 FStar_Util.fold_map extract_one_family env1 ifams in
               (match uu____1853 with
                | (env2,td) -> (env2, [FStar_Extraction_ML_Syntax.MLM_Ty td])))
      | uu____1962 -> failwith "Unexpected signature element"
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
           let uu____1999 = FStar_Syntax_Print.sigelt_to_string se in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____1999);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____2006 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____2015 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____2032 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
           ->
           let extend_env g1 lid ml_name tm tysc =
             let uu____2070 =
               let uu____2075 =
                 FStar_Syntax_Syntax.lid_as_fv lid
                   FStar_Syntax_Syntax.Delta_equational
                   FStar_Pervasives_Native.None in
               FStar_Extraction_ML_UEnv.extend_fv' g1 uu____2075 ml_name tysc
                 false false in
             match uu____2070 with
             | (g2,mangled_name) ->
                 ((let uu____2083 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          g2.FStar_Extraction_ML_UEnv.tcenv)
                       (FStar_Options.Other "ExtractionReify") in
                   if uu____2083
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
             (let uu____2099 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify") in
              if uu____2099
              then
                let uu____2100 = FStar_Syntax_Print.term_to_string tm in
                FStar_Util.print1 "extract_fv term: %s\n" uu____2100
              else ());
             (let uu____2102 =
                let uu____2103 = FStar_Syntax_Subst.compress tm in
                uu____2103.FStar_Syntax_Syntax.n in
              match uu____2102 with
              | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____2111) ->
                  extract_fv tm1
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let mlp =
                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  let uu____2118 =
                    let uu____2127 = FStar_Extraction_ML_UEnv.lookup_fv g fv in
                    FStar_All.pipe_left FStar_Util.right uu____2127 in
                  (match uu____2118 with
                   | (uu____2184,uu____2185,tysc,uu____2187) ->
                       let uu____2188 =
                         FStar_All.pipe_left
                           (FStar_Extraction_ML_Syntax.with_ty
                              FStar_Extraction_ML_Syntax.MLTY_Top)
                           (FStar_Extraction_ML_Syntax.MLE_Name mlp) in
                       (uu____2188, tysc))
              | uu____2189 -> failwith "Not an fv") in
           let extract_action g1 a =
             (let uu____2215 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g1.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify") in
              if uu____2215
              then
                let uu____2216 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_typ in
                let uu____2217 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_defn in
                FStar_Util.print2 "Action type %s and term %s\n" uu____2216
                  uu____2217
              else ());
             (let uu____2219 = FStar_Extraction_ML_UEnv.action_name ed a in
              match uu____2219 with
              | (a_nm,a_lid) ->
                  let lbname =
                    let uu____2235 =
                      FStar_Syntax_Syntax.new_bv
                        (FStar_Pervasives_Native.Some
                           ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                        FStar_Syntax_Syntax.tun in
                    FStar_Util.Inl uu____2235 in
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
                  let uu____2261 =
                    FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb in
                  (match uu____2261 with
                   | (a_let,uu____2273,ty) ->
                       ((let uu____2276 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug
                                g1.FStar_Extraction_ML_UEnv.tcenv)
                             (FStar_Options.Other "ExtractionReify") in
                         if uu____2276
                         then
                           let uu____2277 =
                             FStar_Extraction_ML_Code.string_of_mlexpr a_nm
                               a_let in
                           FStar_Util.print1 "Extracted action term: %s\n"
                             uu____2277
                         else ());
                        (let uu____2279 =
                           match a_let.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_Let
                               ((uu____2288,uu____2289,mllb::[]),uu____2291)
                               ->
                               (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                                with
                                | FStar_Pervasives_Native.Some tysc ->
                                    ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                      tysc)
                                | FStar_Pervasives_Native.None  ->
                                    failwith "No type scheme")
                           | uu____2311 -> failwith "Impossible" in
                         match uu____2279 with
                         | (exp,tysc) ->
                             ((let uu____2323 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug
                                      g1.FStar_Extraction_ML_UEnv.tcenv)
                                   (FStar_Options.Other "ExtractionReify") in
                               if uu____2323
                               then
                                 ((let uu____2325 =
                                     FStar_Extraction_ML_Code.string_of_mlty
                                       a_nm
                                       (FStar_Pervasives_Native.snd tysc) in
                                   FStar_Util.print1
                                     "Extracted action type: %s\n" uu____2325);
                                  FStar_List.iter
                                    (fun x  ->
                                       FStar_Util.print1 "and binders: %s\n"
                                         (FStar_Pervasives_Native.fst x))
                                    (FStar_Pervasives_Native.fst tysc))
                               else ());
                              extend_env g1 a_lid a_nm exp tysc))))) in
           let uu____2337 =
             let uu____2342 =
               extract_fv
                 (FStar_Pervasives_Native.snd
                    ed.FStar_Syntax_Syntax.return_repr) in
             match uu____2342 with
             | (return_tm,ty_sc) ->
                 let uu____2355 =
                   FStar_Extraction_ML_UEnv.monad_op_name ed "return" in
                 (match uu____2355 with
                  | (return_nm,return_lid) ->
                      extend_env g return_lid return_nm return_tm ty_sc) in
           (match uu____2337 with
            | (g1,return_decl) ->
                let uu____2374 =
                  let uu____2379 =
                    extract_fv
                      (FStar_Pervasives_Native.snd
                         ed.FStar_Syntax_Syntax.bind_repr) in
                  match uu____2379 with
                  | (bind_tm,ty_sc) ->
                      let uu____2392 =
                        FStar_Extraction_ML_UEnv.monad_op_name ed "bind" in
                      (match uu____2392 with
                       | (bind_nm,bind_lid) ->
                           extend_env g1 bind_lid bind_nm bind_tm ty_sc) in
                (match uu____2374 with
                 | (g2,bind_decl) ->
                     let uu____2411 =
                       FStar_Util.fold_map extract_action g2
                         ed.FStar_Syntax_Syntax.actions in
                     (match uu____2411 with
                      | (g3,actions) ->
                          (g3,
                            (FStar_List.append [return_decl; bind_decl]
                               actions)))))
       | FStar_Syntax_Syntax.Sig_new_effect uu____2432 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____2436,t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let attrs = se.FStar_Syntax_Syntax.sigattrs in
           let uu____2444 =
             let uu____2445 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___159_2449  ->
                       match uu___159_2449 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____2450 -> false)) in
             Prims.op_Negation uu____2445 in
           if uu____2444
           then (g, [])
           else
             (let uu____2460 = FStar_Syntax_Util.arrow_formals t in
              match uu____2460 with
              | (bs,uu____2480) ->
                  let fv =
                    FStar_Syntax_Syntax.lid_as_fv lid
                      FStar_Syntax_Syntax.Delta_constant
                      FStar_Pervasives_Native.None in
                  let uu____2498 =
                    FStar_Syntax_Util.abs bs FStar_Syntax_Syntax.t_unit
                      FStar_Pervasives_Native.None in
                  extract_typ_abbrev g fv quals attrs uu____2498)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____2500) when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____2516 =
             let uu____2525 =
               FStar_TypeChecker_Env.open_universes_in
                 g.FStar_Extraction_ML_UEnv.tcenv
                 lb.FStar_Syntax_Syntax.lbunivs
                 [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp] in
             match uu____2525 with
             | (tcenv,uu____2549,def_typ) ->
                 let uu____2555 = as_pair def_typ in (tcenv, uu____2555) in
           (match uu____2516 with
            | (tcenv,(lbdef,lbtyp)) ->
                let lbtyp1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.UnfoldUntil
                      FStar_Syntax_Syntax.Delta_constant] tcenv lbtyp in
                let lbdef1 =
                  FStar_TypeChecker_Normalize.eta_expand_with_type tcenv
                    lbdef lbtyp1 in
                let uu____2579 =
                  FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                extract_typ_abbrev g uu____2579 quals
                  se.FStar_Syntax_Syntax.sigattrs lbdef1)
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____2581) ->
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
               | FStar_Syntax_Syntax.Tm_uinst (h',uu____2608) ->
                   let uu____2613 =
                     let uu____2614 = FStar_Syntax_Subst.compress h' in
                     uu____2614.FStar_Syntax_Syntax.n in
                   (match uu____2613 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.tactic_lid
                        ->
                        let uu____2618 =
                          let uu____2619 =
                            FStar_Extraction_ML_Syntax.string_of_mlpath
                              g.FStar_Extraction_ML_UEnv.currentModule in
                          FStar_Util.starts_with uu____2619 "FStar.Tactics" in
                        Prims.op_Negation uu____2618
                    | uu____2620 -> false)
               | uu____2621 -> false in
             let mk_registration tac_lid assm_lid t bs =
               let h =
                 let uu____2650 =
                   let uu____2651 =
                     let uu____2652 =
                       FStar_Ident.lid_of_str
                         "FStar_Tactics_Native.register_tactic" in
                     FStar_Extraction_ML_Syntax.mlpath_of_lident uu____2652 in
                   FStar_Extraction_ML_Syntax.MLE_Name uu____2651 in
                 FStar_All.pipe_left
                   (FStar_Extraction_ML_Syntax.with_ty
                      FStar_Extraction_ML_Syntax.MLTY_Top) uu____2650 in
               let lid_arg =
                 let uu____2654 =
                   let uu____2655 = FStar_Ident.string_of_lid assm_lid in
                   FStar_Extraction_ML_Syntax.MLC_String uu____2655 in
                 FStar_Extraction_ML_Syntax.MLE_Const uu____2654 in
               let tac_arity = FStar_List.length bs in
               let arity =
                 let uu____2662 =
                   let uu____2663 =
                     let uu____2664 =
                       FStar_Util.string_of_int
                         (tac_arity + (Prims.parse_int "1")) in
                     FStar_Ident.lid_of_str uu____2664 in
                   FStar_Extraction_ML_Syntax.mlpath_of_lident uu____2663 in
                 FStar_Extraction_ML_Syntax.MLE_Name uu____2662 in
               let uu____2671 =
                 FStar_Extraction_ML_Util.mk_interpretation_fun tac_lid
                   lid_arg t bs in
               match uu____2671 with
               | FStar_Pervasives_Native.Some tac_interpretation ->
                   let app =
                     let uu____2678 =
                       let uu____2679 =
                         let uu____2686 =
                           FStar_List.map
                             (FStar_Extraction_ML_Syntax.with_ty
                                FStar_Extraction_ML_Syntax.MLTY_Top)
                             [lid_arg; arity; tac_interpretation] in
                         (h, uu____2686) in
                       FStar_Extraction_ML_Syntax.MLE_App uu____2679 in
                     FStar_All.pipe_left
                       (FStar_Extraction_ML_Syntax.with_ty
                          FStar_Extraction_ML_Syntax.MLTY_Top) uu____2678 in
                   [FStar_Extraction_ML_Syntax.MLM_Top app]
               | FStar_Pervasives_Native.None  -> [] in
             match FStar_Pervasives_Native.snd lbs with
             | hd1::[] ->
                 let uu____2696 =
                   FStar_Syntax_Util.arrow_formals_comp
                     hd1.FStar_Syntax_Syntax.lbtyp in
                 (match uu____2696 with
                  | (bs,comp) ->
                      let t = FStar_Syntax_Util.comp_result comp in
                      let uu____2726 =
                        let uu____2727 = FStar_Syntax_Subst.compress t in
                        uu____2727.FStar_Syntax_Syntax.n in
                      (match uu____2726 with
                       | FStar_Syntax_Syntax.Tm_app (h,args) ->
                           let h1 = FStar_Syntax_Subst.compress h in
                           let tac_lid =
                             let uu____2756 =
                               let uu____2759 =
                                 FStar_Util.right
                                   hd1.FStar_Syntax_Syntax.lbname in
                               uu____2759.FStar_Syntax_Syntax.fv_name in
                             uu____2756.FStar_Syntax_Syntax.v in
                           let assm_lid =
                             let uu____2761 =
                               FStar_All.pipe_left FStar_Ident.id_of_text
                                 (Prims.strcat "__"
                                    (tac_lid.FStar_Ident.ident).FStar_Ident.idText) in
                             FStar_Ident.lid_of_ns_and_id
                               tac_lid.FStar_Ident.ns uu____2761 in
                           let uu____2762 = is_tactic_decl assm_lid h1 in
                           if uu____2762
                           then
                             let uu____2765 =
                               let uu____2766 = FStar_List.hd args in
                               FStar_Pervasives_Native.fst uu____2766 in
                             mk_registration tac_lid assm_lid uu____2765 bs
                           else []
                       | uu____2782 -> []))
             | uu____2783 -> [] in
           let uu____2786 = FStar_Extraction_ML_Term.term_as_mlexpr g elet in
           (match uu____2786 with
            | (ml_let,uu____2800,uu____2801) ->
                (match ml_let.FStar_Extraction_ML_Syntax.expr with
                 | FStar_Extraction_ML_Syntax.MLE_Let
                     ((flavor,uu____2809,bindings),uu____2811) ->
                     let uu____2824 =
                       FStar_List.fold_left2
                         (fun uu____2851  ->
                            fun ml_lb  ->
                              fun uu____2853  ->
                                match (uu____2851, uu____2853) with
                                | ((env,ml_lbs),{
                                                  FStar_Syntax_Syntax.lbname
                                                    = lbname;
                                                  FStar_Syntax_Syntax.lbunivs
                                                    = uu____2875;
                                                  FStar_Syntax_Syntax.lbtyp =
                                                    t;
                                                  FStar_Syntax_Syntax.lbeff =
                                                    uu____2877;
                                                  FStar_Syntax_Syntax.lbdef =
                                                    uu____2878;_})
                                    ->
                                    let lb_lid =
                                      let uu____2900 =
                                        let uu____2903 =
                                          FStar_Util.right lbname in
                                        uu____2903.FStar_Syntax_Syntax.fv_name in
                                      uu____2900.FStar_Syntax_Syntax.v in
                                    let uu____2904 =
                                      let uu____2909 =
                                        FStar_All.pipe_right quals
                                          (FStar_Util.for_some
                                             (fun uu___160_2914  ->
                                                match uu___160_2914 with
                                                | FStar_Syntax_Syntax.Projector
                                                    uu____2915 -> true
                                                | uu____2920 -> false)) in
                                      if uu____2909
                                      then
                                        let mname =
                                          let uu____2926 =
                                            mangle_projector_lid lb_lid in
                                          FStar_All.pipe_right uu____2926
                                            FStar_Extraction_ML_Syntax.mlpath_of_lident in
                                        let uu____2927 =
                                          let uu____2932 =
                                            FStar_Util.right lbname in
                                          let uu____2933 =
                                            FStar_Util.must
                                              ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc in
                                          FStar_Extraction_ML_UEnv.extend_fv'
                                            env uu____2932 mname uu____2933
                                            ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                            false in
                                        match uu____2927 with
                                        | (env1,uu____2939) ->
                                            (env1,
                                              (let uu___164_2941 = ml_lb in
                                               {
                                                 FStar_Extraction_ML_Syntax.mllb_name
                                                   =
                                                   ((FStar_Pervasives_Native.snd
                                                       mname),
                                                     (Prims.parse_int "0"));
                                                 FStar_Extraction_ML_Syntax.mllb_tysc
                                                   =
                                                   (uu___164_2941.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                 FStar_Extraction_ML_Syntax.mllb_add_unit
                                                   =
                                                   (uu___164_2941.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                 FStar_Extraction_ML_Syntax.mllb_def
                                                   =
                                                   (uu___164_2941.FStar_Extraction_ML_Syntax.mllb_def);
                                                 FStar_Extraction_ML_Syntax.print_typ
                                                   =
                                                   (uu___164_2941.FStar_Extraction_ML_Syntax.print_typ)
                                               }))
                                      else
                                        (let uu____2945 =
                                           let uu____2946 =
                                             let uu____2951 =
                                               FStar_Util.must
                                                 ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc in
                                             FStar_Extraction_ML_UEnv.extend_lb
                                               env lbname t uu____2951
                                               ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                               false in
                                           FStar_All.pipe_left
                                             FStar_Pervasives_Native.fst
                                             uu____2946 in
                                         (uu____2945, ml_lb)) in
                                    (match uu____2904 with
                                     | (g1,ml_lb1) ->
                                         (g1, (ml_lb1 :: ml_lbs)))) (g, [])
                         bindings (FStar_Pervasives_Native.snd lbs) in
                     (match uu____2824 with
                      | (g1,ml_lbs') ->
                          let flags =
                            FStar_List.choose
                              (fun uu___161_2986  ->
                                 match uu___161_2986 with
                                 | FStar_Syntax_Syntax.Assumption  ->
                                     FStar_Pervasives_Native.Some
                                       FStar_Extraction_ML_Syntax.Assumed
                                 | FStar_Syntax_Syntax.Private  ->
                                     FStar_Pervasives_Native.Some
                                       FStar_Extraction_ML_Syntax.Private
                                 | FStar_Syntax_Syntax.NoExtract  ->
                                     FStar_Pervasives_Native.Some
                                       FStar_Extraction_ML_Syntax.NoExtract
                                 | uu____2989 -> FStar_Pervasives_Native.None)
                              quals in
                          let flags' = extract_metadata attrs in
                          let uu____2993 =
                            let uu____2996 =
                              let uu____2999 =
                                let uu____3000 =
                                  FStar_Extraction_ML_Util.mlloc_of_range
                                    se.FStar_Syntax_Syntax.sigrng in
                                FStar_Extraction_ML_Syntax.MLM_Loc uu____3000 in
                              [uu____2999;
                              FStar_Extraction_ML_Syntax.MLM_Let
                                (flavor, (FStar_List.append flags flags'),
                                  (FStar_List.rev ml_lbs'))] in
                            FStar_List.append uu____2996
                              tactic_registration_decl in
                          (g1, uu____2993))
                 | uu____3007 ->
                     let uu____3008 =
                       let uu____3009 =
                         FStar_Extraction_ML_Code.string_of_mlexpr
                           g.FStar_Extraction_ML_UEnv.currentModule ml_let in
                       FStar_Util.format1
                         "Impossible: Translated a let to a non-let: %s"
                         uu____3009 in
                     failwith uu____3008))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____3017,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____3022 =
             FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption) in
           if uu____3022
           then
             let always_fail =
               let imp =
                 let uu____3033 = FStar_Syntax_Util.arrow_formals t in
                 match uu____3033 with
                 | ([],t1) ->
                     let b =
                       let uu____3062 =
                         FStar_Syntax_Syntax.gen_bv "_"
                           FStar_Pervasives_Native.None t1 in
                       FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                         uu____3062 in
                     let uu____3063 = fail_exp lid t1 in
                     FStar_Syntax_Util.abs [b] uu____3063
                       FStar_Pervasives_Native.None
                 | (bs,t1) ->
                     let uu____3082 = fail_exp lid t1 in
                     FStar_Syntax_Util.abs bs uu____3082
                       FStar_Pervasives_Native.None in
               let uu___165_3083 = se in
               let uu____3084 =
                 let uu____3085 =
                   let uu____3092 =
                     let uu____3099 =
                       let uu____3102 =
                         let uu____3103 =
                           let uu____3108 =
                             FStar_Syntax_Syntax.lid_as_fv lid
                               FStar_Syntax_Syntax.Delta_constant
                               FStar_Pervasives_Native.None in
                           FStar_Util.Inr uu____3108 in
                         {
                           FStar_Syntax_Syntax.lbname = uu____3103;
                           FStar_Syntax_Syntax.lbunivs = [];
                           FStar_Syntax_Syntax.lbtyp = t;
                           FStar_Syntax_Syntax.lbeff =
                             FStar_Parser_Const.effect_ML_lid;
                           FStar_Syntax_Syntax.lbdef = imp
                         } in
                       [uu____3102] in
                     (false, uu____3099) in
                   (uu____3092, []) in
                 FStar_Syntax_Syntax.Sig_let uu____3085 in
               {
                 FStar_Syntax_Syntax.sigel = uu____3084;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___165_3083.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___165_3083.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___165_3083.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___165_3083.FStar_Syntax_Syntax.sigattrs)
               } in
             let uu____3119 = extract_sig g always_fail in
             (match uu____3119 with
              | (g1,mlm) ->
                  let uu____3138 =
                    FStar_Util.find_map quals
                      (fun uu___162_3143  ->
                         match uu___162_3143 with
                         | FStar_Syntax_Syntax.Discriminator l ->
                             FStar_Pervasives_Native.Some l
                         | uu____3147 -> FStar_Pervasives_Native.None) in
                  (match uu____3138 with
                   | FStar_Pervasives_Native.Some l ->
                       let uu____3155 =
                         let uu____3158 =
                           let uu____3159 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____3159 in
                         let uu____3160 =
                           let uu____3163 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l in
                           [uu____3163] in
                         uu____3158 :: uu____3160 in
                       (g1, uu____3155)
                   | uu____3166 ->
                       let uu____3169 =
                         FStar_Util.find_map quals
                           (fun uu___163_3175  ->
                              match uu___163_3175 with
                              | FStar_Syntax_Syntax.Projector (l,uu____3179)
                                  -> FStar_Pervasives_Native.Some l
                              | uu____3180 -> FStar_Pervasives_Native.None) in
                       (match uu____3169 with
                        | FStar_Pervasives_Native.Some uu____3187 -> (g1, [])
                        | uu____3190 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____3199 = FStar_Extraction_ML_Term.term_as_mlexpr g e in
           (match uu____3199 with
            | (ml_main,uu____3213,uu____3214) ->
                let uu____3215 =
                  let uu____3218 =
                    let uu____3219 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____3219 in
                  [uu____3218; FStar_Extraction_ML_Syntax.MLM_Top ml_main] in
                (g, uu____3215))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____3222 ->
           failwith "impossible -- removed by tc.fs"
       | FStar_Syntax_Syntax.Sig_assume uu____3229 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____3238 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____3241 -> (g, [])
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (if p = FStar_Syntax_Syntax.LightOff
            then FStar_Options.set_ml_ish ()
            else ();
            (g, [])))
let extract_iface:
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.modul -> env_t =
  fun g  ->
    fun m  ->
      let uu____3269 =
        FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____3269 FStar_Pervasives_Native.fst
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
      (let uu____3314 = FStar_Options.debug_any () in
       if uu____3314
       then
         let uu____3315 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
         FStar_Util.print1 "Extracting module %s\n" uu____3315
       else ());
      (let codegen_opt = FStar_Options.codegen () in
       let uu____3320 = FStar_Options.restore_cmd_line_options true in
       (match codegen_opt with
        | FStar_Pervasives_Native.Some "OCaml" ->
            FStar_Options.set_option "codegen" (FStar_Options.String "OCaml")
        | uu____3322 -> ());
       (let name =
          FStar_Extraction_ML_Syntax.mlpath_of_lident
            m.FStar_Syntax_Syntax.name in
        let g1 =
          let uu___166_3327 = g in
          let uu____3328 =
            FStar_TypeChecker_Env.set_current_module
              g.FStar_Extraction_ML_UEnv.tcenv m.FStar_Syntax_Syntax.name in
          {
            FStar_Extraction_ML_UEnv.tcenv = uu____3328;
            FStar_Extraction_ML_UEnv.gamma =
              (uu___166_3327.FStar_Extraction_ML_UEnv.gamma);
            FStar_Extraction_ML_UEnv.tydefs =
              (uu___166_3327.FStar_Extraction_ML_UEnv.tydefs);
            FStar_Extraction_ML_UEnv.type_names =
              (uu___166_3327.FStar_Extraction_ML_UEnv.type_names);
            FStar_Extraction_ML_UEnv.currentModule = name
          } in
        let uu____3329 =
          FStar_Util.fold_map extract_sig g1
            m.FStar_Syntax_Syntax.declarations in
        match uu____3329 with
        | (g2,sigs) ->
            let mlm = FStar_List.flatten sigs in
            let is_kremlin =
              let uu____3358 = FStar_Options.codegen () in
              match uu____3358 with
              | FStar_Pervasives_Native.Some "Kremlin" -> true
              | uu____3361 -> false in
            let uu____3364 =
              (((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
                 (is_kremlin ||
                    (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)))
                &&
                (FStar_Options.should_extract
                   (m.FStar_Syntax_Syntax.name).FStar_Ident.str) in
            if uu____3364
            then
              ((let uu____3372 =
                  FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
                FStar_Util.print1 "Extracted module %s\n" uu____3372);
               (g2,
                 [FStar_Extraction_ML_Syntax.MLLib
                    [(name, (FStar_Pervasives_Native.Some ([], mlm)),
                       (FStar_Extraction_ML_Syntax.MLLib []))]]))
            else (g2, [])))