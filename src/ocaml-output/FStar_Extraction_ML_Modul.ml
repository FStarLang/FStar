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
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string (data,uu____174));
        FStar_Syntax_Syntax.pos = uu____175;
        FStar_Syntax_Syntax.vars = uu____176;_} when data = "c_inline" ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CInline
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string (data,uu____180));
        FStar_Syntax_Syntax.pos = uu____181;
        FStar_Syntax_Syntax.vars = uu____182;_} when data = "substitute" ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Substitute
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_meta (x1,uu____186);
        FStar_Syntax_Syntax.pos = uu____187;
        FStar_Syntax_Syntax.vars = uu____188;_} -> extract_meta x1
    | a ->
        ((let uu____197 = FStar_Syntax_Print.term_to_string a in
          FStar_Util.print1_warning
            "Warning: unrecognized attribute (%s), valid attributes are `c_inline`, `substitute`, and `gc`."
            uu____197);
         FStar_Pervasives_Native.None)
let extract_metadata:
  FStar_Syntax_Syntax.term Prims.list ->
    FStar_Extraction_ML_Syntax.meta Prims.list
  = fun metas  -> FStar_List.choose extract_meta metas
let binders_as_mlty_binders:
  'Auu____214 .
    FStar_Extraction_ML_UEnv.env ->
      (FStar_Syntax_Syntax.bv,'Auu____214) FStar_Pervasives_Native.tuple2
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
           fun uu____260  ->
             match uu____260 with
             | (bv,uu____274) ->
                 let uu____275 =
                   let uu____276 =
                     let uu____279 =
                       let uu____280 =
                         FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv in
                       FStar_Extraction_ML_Syntax.MLTY_Var uu____280 in
                     FStar_Pervasives_Native.Some uu____279 in
                   FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____276 in
                 let uu____281 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv in
                 (uu____275, uu____281)) env bs
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
              let uu____326 =
                let uu____327 = FStar_Syntax_Subst.compress def in
                FStar_All.pipe_right uu____327 FStar_Syntax_Util.unmeta in
              FStar_All.pipe_right uu____326 FStar_Syntax_Util.un_uinst in
            let def2 =
              match def1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_abs uu____329 ->
                  FStar_Extraction_ML_Term.normalize_abs def1
              | uu____346 -> def1 in
            let uu____347 =
              match def2.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____358) ->
                  FStar_Syntax_Subst.open_term bs body
              | uu____379 -> ([], def2) in
            match uu____347 with
            | (bs,body) ->
                let assumed =
                  FStar_Util.for_some
                    (fun uu___155_400  ->
                       match uu___155_400 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____401 -> false) quals in
                let uu____402 = binders_as_mlty_binders env bs in
                (match uu____402 with
                 | (env1,ml_bs) ->
                     let body1 =
                       let uu____434 =
                         FStar_Extraction_ML_Term.term_as_mlty env1 body in
                       FStar_All.pipe_right uu____434
                         (FStar_Extraction_ML_Util.eraseTypeDeep
                            (FStar_Extraction_ML_Util.udelta_unfold env1)) in
                     let mangled_projector =
                       let uu____438 =
                         FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___156_443  ->
                                 match uu___156_443 with
                                 | FStar_Syntax_Syntax.Projector uu____444 ->
                                     true
                                 | uu____449 -> false)) in
                       if uu____438
                       then
                         let mname = mangle_projector_lid lid in
                         FStar_Pervasives_Native.Some
                           ((mname.FStar_Ident.ident).FStar_Ident.idText)
                       else FStar_Pervasives_Native.None in
                     let metadata = extract_metadata attrs in
                     let td =
                       let uu____484 =
                         let uu____509 = lident_as_mlsymbol lid in
                         (assumed, uu____509, mangled_projector, ml_bs,
                           metadata,
                           (FStar_Pervasives_Native.Some
                              (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1))) in
                       [uu____484] in
                     let def3 =
                       let uu____573 =
                         let uu____574 =
                           FStar_Extraction_ML_Util.mlloc_of_range
                             (FStar_Ident.range_of_lid lid) in
                         FStar_Extraction_ML_Syntax.MLM_Loc uu____574 in
                       [uu____573; FStar_Extraction_ML_Syntax.MLM_Ty td] in
                     let env2 =
                       let uu____576 =
                         FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___157_580  ->
                                 match uu___157_580 with
                                 | FStar_Syntax_Syntax.Assumption  -> true
                                 | FStar_Syntax_Syntax.New  -> true
                                 | uu____581 -> false)) in
                       if uu____576
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
  imetadata: FStar_Extraction_ML_Syntax.metadata;}
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
    let uu____729 = FStar_Syntax_Print.lid_to_string i.iname in
    let uu____730 = FStar_Syntax_Print.binders_to_string " " i.iparams in
    let uu____731 = FStar_Syntax_Print.term_to_string i.ityp in
    let uu____732 =
      let uu____733 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let uu____744 = FStar_Syntax_Print.lid_to_string d.dname in
                let uu____745 =
                  let uu____746 = FStar_Syntax_Print.term_to_string d.dtyp in
                  Prims.strcat " : " uu____746 in
                Prims.strcat uu____744 uu____745)) in
      FStar_All.pipe_right uu____733 (FStar_String.concat "\n\t\t") in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____729 uu____730 uu____731
      uu____732
let bundle_as_inductive_families:
  'Auu____759 .
    FStar_Extraction_ML_UEnv.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'Auu____759 ->
          FStar_Syntax_Syntax.attribute Prims.list ->
            (FStar_Extraction_ML_UEnv.env,inductive_family Prims.list)
              FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun attrs  ->
          let uu____790 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun se  ->
                   match se.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,_us,bs,t,_mut_i,datas) ->
                       let uu____837 = FStar_Syntax_Subst.open_term bs t in
                       (match uu____837 with
                        | (bs1,t1) ->
                            let datas1 =
                              FStar_All.pipe_right ses
                                (FStar_List.collect
                                   (fun se1  ->
                                      match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_datacon
                                          (d,uu____876,t2,l',nparams,uu____880)
                                          when FStar_Ident.lid_equals l l' ->
                                          let uu____885 =
                                            FStar_Syntax_Util.arrow_formals
                                              t2 in
                                          (match uu____885 with
                                           | (bs',body) ->
                                               let uu____918 =
                                                 FStar_Util.first_N
                                                   (FStar_List.length bs1)
                                                   bs' in
                                               (match uu____918 with
                                                | (bs_params,rest) ->
                                                    let subst1 =
                                                      FStar_List.map2
                                                        (fun uu____989  ->
                                                           fun uu____990  ->
                                                             match (uu____989,
                                                                    uu____990)
                                                             with
                                                             | ((b',uu____1008),
                                                                (b,uu____1010))
                                                                 ->
                                                                 let uu____1019
                                                                   =
                                                                   let uu____1026
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b in
                                                                   (b',
                                                                    uu____1026) in
                                                                 FStar_Syntax_Syntax.NT
                                                                   uu____1019)
                                                        bs_params bs1 in
                                                    let t3 =
                                                      let uu____1028 =
                                                        let uu____1031 =
                                                          FStar_Syntax_Syntax.mk_Total
                                                            body in
                                                        FStar_Syntax_Util.arrow
                                                          rest uu____1031 in
                                                      FStar_All.pipe_right
                                                        uu____1028
                                                        (FStar_Syntax_Subst.subst
                                                           subst1) in
                                                    [{ dname = d; dtyp = t3 }]))
                                      | uu____1036 -> [])) in
                            let metadata =
                              extract_metadata
                                (FStar_List.append
                                   se.FStar_Syntax_Syntax.sigattrs attrs) in
                            let env2 =
                              let uu____1041 =
                                FStar_Syntax_Syntax.lid_as_fv l
                                  FStar_Syntax_Syntax.Delta_constant
                                  FStar_Pervasives_Native.None in
                              FStar_Extraction_ML_UEnv.extend_type_name env1
                                uu____1041 in
                            (env2,
                              [{
                                 iname = l;
                                 iparams = bs1;
                                 ityp = t1;
                                 idatas = datas1;
                                 iquals = (se.FStar_Syntax_Syntax.sigquals);
                                 imetadata = metadata
                               }]))
                   | uu____1044 -> (env1, [])) env ses in
          match uu____790 with
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
          let uu____1130 =
            FStar_Extraction_ML_Term.term_as_mlty env1 ctor.dtyp in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env1) uu____1130 in
        let steps =
          [FStar_TypeChecker_Normalize.Inlining;
          FStar_TypeChecker_Normalize.UnfoldUntil
            FStar_Syntax_Syntax.Delta_constant;
          FStar_TypeChecker_Normalize.EraseUniverses;
          FStar_TypeChecker_Normalize.AllowUnboundUniverses] in
        let names1 =
          let uu____1137 =
            let uu____1138 =
              let uu____1141 =
                FStar_TypeChecker_Normalize.normalize steps
                  env1.FStar_Extraction_ML_UEnv.tcenv ctor.dtyp in
              FStar_Syntax_Subst.compress uu____1141 in
            uu____1138.FStar_Syntax_Syntax.n in
          match uu____1137 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,uu____1145) ->
              FStar_List.map
                (fun uu____1171  ->
                   match uu____1171 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____1177;
                        FStar_Syntax_Syntax.sort = uu____1178;_},uu____1179)
                       -> ppname.FStar_Ident.idText) bs
          | uu____1182 -> [] in
        let tys = (ml_tyvars, mlt) in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp in
        let uu____1201 =
          let uu____1202 =
            FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false in
          FStar_Pervasives_Native.fst uu____1202 in
        let uu____1207 =
          let uu____1218 = lident_as_mlsymbol ctor.dname in
          let uu____1219 =
            let uu____1226 = FStar_Extraction_ML_Util.argTypes mlt in
            FStar_List.zip names1 uu____1226 in
          (uu____1218, uu____1219) in
        (uu____1201, uu____1207) in
      let extract_one_family env1 ind =
        let uu____1278 = binders_as_mlty_binders env1 ind.iparams in
        match uu____1278 with
        | (env2,vars) ->
            let uu____1329 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor vars) env2) in
            (match uu____1329 with
             | (env3,ctors) ->
                 let uu____1426 = FStar_Syntax_Util.arrow_formals ind.ityp in
                 (match uu____1426 with
                  | (indices,uu____1466) ->
                      let ml_params =
                        let uu____1490 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____1521  ->
                                    let uu____1526 =
                                      let uu____1527 =
                                        FStar_Util.string_of_int i in
                                      Prims.strcat "'dummyV" uu____1527 in
                                    (uu____1526, (Prims.parse_int "0")))) in
                        FStar_List.append vars uu____1490 in
                      let tbody =
                        let uu____1533 =
                          FStar_Util.find_opt
                            (fun uu___158_1538  ->
                               match uu___158_1538 with
                               | FStar_Syntax_Syntax.RecordType uu____1539 ->
                                   true
                               | uu____1548 -> false) ind.iquals in
                        match uu____1533 with
                        | FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____1559 = FStar_List.hd ctors in
                            (match uu____1559 with
                             | (uu____1580,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id  ->
                                        fun uu____1619  ->
                                          match uu____1619 with
                                          | (uu____1628,ty) ->
                                              let lid =
                                                FStar_Ident.lid_of_ids
                                                  (FStar_List.append ns [id]) in
                                              let uu____1631 =
                                                lident_as_mlsymbol lid in
                                              (uu____1631, ty)) ids c_ty in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____1632 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors in
                      let uu____1635 =
                        let uu____1658 = lident_as_mlsymbol ind.iname in
                        (false, uu____1658, FStar_Pervasives_Native.None,
                          ml_params, (ind.imetadata),
                          (FStar_Pervasives_Native.Some tbody)) in
                      (env3, uu____1635))) in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____1700,t,uu____1702,uu____1703,uu____1704);
            FStar_Syntax_Syntax.sigrng = uu____1705;
            FStar_Syntax_Syntax.sigquals = uu____1706;
            FStar_Syntax_Syntax.sigmeta = uu____1707;
            FStar_Syntax_Syntax.sigattrs = uu____1708;_}::[],uu____1709),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____1726 = extract_ctor [] env { dname = l; dtyp = t } in
          (match uu____1726 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____1776),quals) ->
          let uu____1790 =
            bundle_as_inductive_families env ses quals
              se.FStar_Syntax_Syntax.sigattrs in
          (match uu____1790 with
           | (env1,ifams) ->
               let uu____1811 =
                 FStar_Util.fold_map extract_one_family env1 ifams in
               (match uu____1811 with
                | (env2,td) -> (env2, [FStar_Extraction_ML_Syntax.MLM_Ty td])))
      | uu____1920 -> failwith "Unexpected signature element"
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
           let uu____1957 = FStar_Syntax_Print.sigelt_to_string se in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____1957);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____1964 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____1973 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____1990 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
           ->
           let extend_env g1 lid ml_name tm tysc =
             let uu____2028 =
               let uu____2033 =
                 FStar_Syntax_Syntax.lid_as_fv lid
                   FStar_Syntax_Syntax.Delta_equational
                   FStar_Pervasives_Native.None in
               FStar_Extraction_ML_UEnv.extend_fv' g1 uu____2033 ml_name tysc
                 false false in
             match uu____2028 with
             | (g2,mangled_name) ->
                 ((let uu____2041 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          g2.FStar_Extraction_ML_UEnv.tcenv)
                       (FStar_Options.Other "ExtractionReify") in
                   if uu____2041
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
             (let uu____2057 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify") in
              if uu____2057
              then
                let uu____2058 = FStar_Syntax_Print.term_to_string tm in
                FStar_Util.print1 "extract_fv term: %s\n" uu____2058
              else ());
             (let uu____2060 =
                let uu____2061 = FStar_Syntax_Subst.compress tm in
                uu____2061.FStar_Syntax_Syntax.n in
              match uu____2060 with
              | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____2069) ->
                  extract_fv tm1
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let mlp =
                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  let uu____2076 =
                    let uu____2085 = FStar_Extraction_ML_UEnv.lookup_fv g fv in
                    FStar_All.pipe_left FStar_Util.right uu____2085 in
                  (match uu____2076 with
                   | (uu____2142,uu____2143,tysc,uu____2145) ->
                       let uu____2146 =
                         FStar_All.pipe_left
                           (FStar_Extraction_ML_Syntax.with_ty
                              FStar_Extraction_ML_Syntax.MLTY_Top)
                           (FStar_Extraction_ML_Syntax.MLE_Name mlp) in
                       (uu____2146, tysc))
              | uu____2147 -> failwith "Not an fv") in
           let extract_action g1 a =
             (let uu____2173 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g1.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify") in
              if uu____2173
              then
                let uu____2174 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_typ in
                let uu____2175 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_defn in
                FStar_Util.print2 "Action type %s and term %s\n" uu____2174
                  uu____2175
              else ());
             (let uu____2177 = FStar_Extraction_ML_UEnv.action_name ed a in
              match uu____2177 with
              | (a_nm,a_lid) ->
                  let lbname =
                    let uu____2193 =
                      FStar_Syntax_Syntax.new_bv
                        (FStar_Pervasives_Native.Some
                           ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                        FStar_Syntax_Syntax.tun in
                    FStar_Util.Inl uu____2193 in
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
                  let uu____2219 =
                    FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb in
                  (match uu____2219 with
                   | (a_let,uu____2231,ty) ->
                       ((let uu____2234 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug
                                g1.FStar_Extraction_ML_UEnv.tcenv)
                             (FStar_Options.Other "ExtractionReify") in
                         if uu____2234
                         then
                           let uu____2235 =
                             FStar_Extraction_ML_Code.string_of_mlexpr a_nm
                               a_let in
                           FStar_Util.print1 "Extracted action term: %s\n"
                             uu____2235
                         else ());
                        (let uu____2237 =
                           match a_let.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_Let
                               ((uu____2246,uu____2247,mllb::[]),uu____2249)
                               ->
                               (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                                with
                                | FStar_Pervasives_Native.Some tysc ->
                                    ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                      tysc)
                                | FStar_Pervasives_Native.None  ->
                                    failwith "No type scheme")
                           | uu____2269 -> failwith "Impossible" in
                         match uu____2237 with
                         | (exp,tysc) ->
                             ((let uu____2281 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug
                                      g1.FStar_Extraction_ML_UEnv.tcenv)
                                   (FStar_Options.Other "ExtractionReify") in
                               if uu____2281
                               then
                                 ((let uu____2283 =
                                     FStar_Extraction_ML_Code.string_of_mlty
                                       a_nm
                                       (FStar_Pervasives_Native.snd tysc) in
                                   FStar_Util.print1
                                     "Extracted action type: %s\n" uu____2283);
                                  FStar_List.iter
                                    (fun x  ->
                                       FStar_Util.print1 "and binders: %s\n"
                                         (FStar_Pervasives_Native.fst x))
                                    (FStar_Pervasives_Native.fst tysc))
                               else ());
                              extend_env g1 a_lid a_nm exp tysc))))) in
           let uu____2295 =
             let uu____2300 =
               extract_fv
                 (FStar_Pervasives_Native.snd
                    ed.FStar_Syntax_Syntax.return_repr) in
             match uu____2300 with
             | (return_tm,ty_sc) ->
                 let uu____2313 =
                   FStar_Extraction_ML_UEnv.monad_op_name ed "return" in
                 (match uu____2313 with
                  | (return_nm,return_lid) ->
                      extend_env g return_lid return_nm return_tm ty_sc) in
           (match uu____2295 with
            | (g1,return_decl) ->
                let uu____2332 =
                  let uu____2337 =
                    extract_fv
                      (FStar_Pervasives_Native.snd
                         ed.FStar_Syntax_Syntax.bind_repr) in
                  match uu____2337 with
                  | (bind_tm,ty_sc) ->
                      let uu____2350 =
                        FStar_Extraction_ML_UEnv.monad_op_name ed "bind" in
                      (match uu____2350 with
                       | (bind_nm,bind_lid) ->
                           extend_env g1 bind_lid bind_nm bind_tm ty_sc) in
                (match uu____2332 with
                 | (g2,bind_decl) ->
                     let uu____2369 =
                       FStar_Util.fold_map extract_action g2
                         ed.FStar_Syntax_Syntax.actions in
                     (match uu____2369 with
                      | (g3,actions) ->
                          (g3,
                            (FStar_List.append [return_decl; bind_decl]
                               actions)))))
       | FStar_Syntax_Syntax.Sig_new_effect uu____2390 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____2394,t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let attrs = se.FStar_Syntax_Syntax.sigattrs in
           let uu____2402 =
             let uu____2403 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___159_2407  ->
                       match uu___159_2407 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____2408 -> false)) in
             Prims.op_Negation uu____2403 in
           if uu____2402
           then (g, [])
           else
             (let uu____2418 = FStar_Syntax_Util.arrow_formals t in
              match uu____2418 with
              | (bs,uu____2438) ->
                  let fv =
                    FStar_Syntax_Syntax.lid_as_fv lid
                      FStar_Syntax_Syntax.Delta_constant
                      FStar_Pervasives_Native.None in
                  let uu____2456 =
                    FStar_Syntax_Util.abs bs FStar_Syntax_Syntax.t_unit
                      FStar_Pervasives_Native.None in
                  extract_typ_abbrev g fv quals attrs uu____2456)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____2458) when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____2474 =
             let uu____2483 =
               FStar_TypeChecker_Env.open_universes_in
                 g.FStar_Extraction_ML_UEnv.tcenv
                 lb.FStar_Syntax_Syntax.lbunivs
                 [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp] in
             match uu____2483 with
             | (tcenv,uu____2507,def_typ) ->
                 let uu____2513 = as_pair def_typ in (tcenv, uu____2513) in
           (match uu____2474 with
            | (tcenv,(lbdef,lbtyp)) ->
                let lbtyp1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.UnfoldUntil
                      FStar_Syntax_Syntax.Delta_constant] tcenv lbtyp in
                let lbdef1 =
                  FStar_TypeChecker_Normalize.eta_expand_with_type tcenv
                    lbdef lbtyp1 in
                let uu____2537 =
                  FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                extract_typ_abbrev g uu____2537 quals
                  se.FStar_Syntax_Syntax.sigattrs lbdef1)
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____2539) ->
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
               | FStar_Syntax_Syntax.Tm_uinst (h',uu____2566) ->
                   let uu____2571 =
                     let uu____2572 = FStar_Syntax_Subst.compress h' in
                     uu____2572.FStar_Syntax_Syntax.n in
                   (match uu____2571 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.tactic_lid
                        ->
                        let uu____2576 =
                          let uu____2577 =
                            FStar_Extraction_ML_Syntax.string_of_mlpath
                              g.FStar_Extraction_ML_UEnv.currentModule in
                          FStar_Util.starts_with uu____2577 "FStar.Tactics" in
                        Prims.op_Negation uu____2576
                    | uu____2578 -> false)
               | uu____2579 -> false in
             let mk_registration tac_lid assm_lid t bs =
               let h =
                 let uu____2608 =
                   let uu____2609 =
                     let uu____2610 =
                       FStar_Ident.lid_of_str
                         "FStar_Tactics_Native.register_tactic" in
                     FStar_Extraction_ML_Syntax.mlpath_of_lident uu____2610 in
                   FStar_Extraction_ML_Syntax.MLE_Name uu____2609 in
                 FStar_All.pipe_left
                   (FStar_Extraction_ML_Syntax.with_ty
                      FStar_Extraction_ML_Syntax.MLTY_Top) uu____2608 in
               let lid_arg =
                 let uu____2612 =
                   let uu____2613 = FStar_Ident.string_of_lid assm_lid in
                   FStar_Extraction_ML_Syntax.MLC_String uu____2613 in
                 FStar_Extraction_ML_Syntax.MLE_Const uu____2612 in
               let tac_arity = FStar_List.length bs in
               let arity =
                 let uu____2620 =
                   let uu____2621 =
                     let uu____2622 =
                       FStar_Util.string_of_int
                         (tac_arity + (Prims.parse_int "1")) in
                     FStar_Ident.lid_of_str uu____2622 in
                   FStar_Extraction_ML_Syntax.mlpath_of_lident uu____2621 in
                 FStar_Extraction_ML_Syntax.MLE_Name uu____2620 in
               let uu____2629 =
                 FStar_Extraction_ML_Util.mk_interpretation_fun tac_lid
                   lid_arg t bs in
               match uu____2629 with
               | FStar_Pervasives_Native.Some tac_interpretation ->
                   let app =
                     let uu____2636 =
                       let uu____2637 =
                         let uu____2644 =
                           FStar_List.map
                             (FStar_Extraction_ML_Syntax.with_ty
                                FStar_Extraction_ML_Syntax.MLTY_Top)
                             [lid_arg; arity; tac_interpretation] in
                         (h, uu____2644) in
                       FStar_Extraction_ML_Syntax.MLE_App uu____2637 in
                     FStar_All.pipe_left
                       (FStar_Extraction_ML_Syntax.with_ty
                          FStar_Extraction_ML_Syntax.MLTY_Top) uu____2636 in
                   [FStar_Extraction_ML_Syntax.MLM_Top app]
               | FStar_Pervasives_Native.None  -> [] in
             match FStar_Pervasives_Native.snd lbs with
             | hd1::[] ->
                 let uu____2654 =
                   FStar_Syntax_Util.arrow_formals_comp
                     hd1.FStar_Syntax_Syntax.lbtyp in
                 (match uu____2654 with
                  | (bs,comp) ->
                      let t = FStar_Syntax_Util.comp_result comp in
                      let uu____2684 =
                        let uu____2685 = FStar_Syntax_Subst.compress t in
                        uu____2685.FStar_Syntax_Syntax.n in
                      (match uu____2684 with
                       | FStar_Syntax_Syntax.Tm_app (h,args) ->
                           let h1 = FStar_Syntax_Subst.compress h in
                           let tac_lid =
                             let uu____2714 =
                               let uu____2717 =
                                 FStar_Util.right
                                   hd1.FStar_Syntax_Syntax.lbname in
                               uu____2717.FStar_Syntax_Syntax.fv_name in
                             uu____2714.FStar_Syntax_Syntax.v in
                           let assm_lid =
                             let uu____2719 =
                               FStar_All.pipe_left FStar_Ident.id_of_text
                                 (Prims.strcat "__"
                                    (tac_lid.FStar_Ident.ident).FStar_Ident.idText) in
                             FStar_Ident.lid_of_ns_and_id
                               tac_lid.FStar_Ident.ns uu____2719 in
                           let uu____2720 = is_tactic_decl assm_lid h1 in
                           if uu____2720
                           then
                             let uu____2723 =
                               let uu____2724 = FStar_List.hd args in
                               FStar_Pervasives_Native.fst uu____2724 in
                             mk_registration tac_lid assm_lid uu____2723 bs
                           else []
                       | uu____2740 -> []))
             | uu____2741 -> [] in
           let uu____2744 = FStar_Extraction_ML_Term.term_as_mlexpr g elet in
           (match uu____2744 with
            | (ml_let,uu____2758,uu____2759) ->
                (match ml_let.FStar_Extraction_ML_Syntax.expr with
                 | FStar_Extraction_ML_Syntax.MLE_Let
                     ((flavor,uu____2767,bindings),uu____2769) ->
                     let uu____2782 =
                       FStar_List.fold_left2
                         (fun uu____2809  ->
                            fun ml_lb  ->
                              fun uu____2811  ->
                                match (uu____2809, uu____2811) with
                                | ((env,ml_lbs),{
                                                  FStar_Syntax_Syntax.lbname
                                                    = lbname;
                                                  FStar_Syntax_Syntax.lbunivs
                                                    = uu____2833;
                                                  FStar_Syntax_Syntax.lbtyp =
                                                    t;
                                                  FStar_Syntax_Syntax.lbeff =
                                                    uu____2835;
                                                  FStar_Syntax_Syntax.lbdef =
                                                    uu____2836;_})
                                    ->
                                    let lb_lid =
                                      let uu____2858 =
                                        let uu____2861 =
                                          FStar_Util.right lbname in
                                        uu____2861.FStar_Syntax_Syntax.fv_name in
                                      uu____2858.FStar_Syntax_Syntax.v in
                                    let uu____2862 =
                                      let uu____2867 =
                                        FStar_All.pipe_right quals
                                          (FStar_Util.for_some
                                             (fun uu___160_2872  ->
                                                match uu___160_2872 with
                                                | FStar_Syntax_Syntax.Projector
                                                    uu____2873 -> true
                                                | uu____2878 -> false)) in
                                      if uu____2867
                                      then
                                        let mname =
                                          let uu____2884 =
                                            mangle_projector_lid lb_lid in
                                          FStar_All.pipe_right uu____2884
                                            FStar_Extraction_ML_Syntax.mlpath_of_lident in
                                        let uu____2885 =
                                          let uu____2890 =
                                            FStar_Util.right lbname in
                                          let uu____2891 =
                                            FStar_Util.must
                                              ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc in
                                          FStar_Extraction_ML_UEnv.extend_fv'
                                            env uu____2890 mname uu____2891
                                            ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                            false in
                                        match uu____2885 with
                                        | (env1,uu____2897) ->
                                            (env1,
                                              (let uu___164_2899 = ml_lb in
                                               {
                                                 FStar_Extraction_ML_Syntax.mllb_name
                                                   =
                                                   ((FStar_Pervasives_Native.snd
                                                       mname),
                                                     (Prims.parse_int "0"));
                                                 FStar_Extraction_ML_Syntax.mllb_tysc
                                                   =
                                                   (uu___164_2899.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                 FStar_Extraction_ML_Syntax.mllb_add_unit
                                                   =
                                                   (uu___164_2899.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                 FStar_Extraction_ML_Syntax.mllb_def
                                                   =
                                                   (uu___164_2899.FStar_Extraction_ML_Syntax.mllb_def);
                                                 FStar_Extraction_ML_Syntax.print_typ
                                                   =
                                                   (uu___164_2899.FStar_Extraction_ML_Syntax.print_typ)
                                               }))
                                      else
                                        (let uu____2903 =
                                           let uu____2904 =
                                             let uu____2909 =
                                               FStar_Util.must
                                                 ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc in
                                             FStar_Extraction_ML_UEnv.extend_lb
                                               env lbname t uu____2909
                                               ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                               false in
                                           FStar_All.pipe_left
                                             FStar_Pervasives_Native.fst
                                             uu____2904 in
                                         (uu____2903, ml_lb)) in
                                    (match uu____2862 with
                                     | (g1,ml_lb1) ->
                                         (g1, (ml_lb1 :: ml_lbs)))) (g, [])
                         bindings (FStar_Pervasives_Native.snd lbs) in
                     (match uu____2782 with
                      | (g1,ml_lbs') ->
                          let flags =
                            FStar_List.choose
                              (fun uu___161_2944  ->
                                 match uu___161_2944 with
                                 | FStar_Syntax_Syntax.Assumption  ->
                                     FStar_Pervasives_Native.Some
                                       FStar_Extraction_ML_Syntax.Assumed
                                 | FStar_Syntax_Syntax.Private  ->
                                     FStar_Pervasives_Native.Some
                                       FStar_Extraction_ML_Syntax.Private
                                 | FStar_Syntax_Syntax.NoExtract  ->
                                     FStar_Pervasives_Native.Some
                                       FStar_Extraction_ML_Syntax.NoExtract
                                 | uu____2947 -> FStar_Pervasives_Native.None)
                              quals in
                          let flags' = extract_metadata attrs in
                          let uu____2951 =
                            let uu____2954 =
                              let uu____2957 =
                                let uu____2958 =
                                  FStar_Extraction_ML_Util.mlloc_of_range
                                    se.FStar_Syntax_Syntax.sigrng in
                                FStar_Extraction_ML_Syntax.MLM_Loc uu____2958 in
                              [uu____2957;
                              FStar_Extraction_ML_Syntax.MLM_Let
                                (flavor, (FStar_List.append flags flags'),
                                  (FStar_List.rev ml_lbs'))] in
                            FStar_List.append uu____2954
                              tactic_registration_decl in
                          (g1, uu____2951))
                 | uu____2965 ->
                     let uu____2966 =
                       let uu____2967 =
                         FStar_Extraction_ML_Code.string_of_mlexpr
                           g.FStar_Extraction_ML_UEnv.currentModule ml_let in
                       FStar_Util.format1
                         "Impossible: Translated a let to a non-let: %s"
                         uu____2967 in
                     failwith uu____2966))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____2975,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____2980 =
             FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption) in
           if uu____2980
           then
             let always_fail =
               let imp =
                 let uu____2991 = FStar_Syntax_Util.arrow_formals t in
                 match uu____2991 with
                 | ([],t1) ->
                     let b =
                       let uu____3020 =
                         FStar_Syntax_Syntax.gen_bv "_"
                           FStar_Pervasives_Native.None t1 in
                       FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                         uu____3020 in
                     let uu____3021 = fail_exp lid t1 in
                     FStar_Syntax_Util.abs [b] uu____3021
                       FStar_Pervasives_Native.None
                 | (bs,t1) ->
                     let uu____3040 = fail_exp lid t1 in
                     FStar_Syntax_Util.abs bs uu____3040
                       FStar_Pervasives_Native.None in
               let uu___165_3041 = se in
               let uu____3042 =
                 let uu____3043 =
                   let uu____3050 =
                     let uu____3057 =
                       let uu____3060 =
                         let uu____3061 =
                           let uu____3066 =
                             FStar_Syntax_Syntax.lid_as_fv lid
                               FStar_Syntax_Syntax.Delta_constant
                               FStar_Pervasives_Native.None in
                           FStar_Util.Inr uu____3066 in
                         {
                           FStar_Syntax_Syntax.lbname = uu____3061;
                           FStar_Syntax_Syntax.lbunivs = [];
                           FStar_Syntax_Syntax.lbtyp = t;
                           FStar_Syntax_Syntax.lbeff =
                             FStar_Parser_Const.effect_ML_lid;
                           FStar_Syntax_Syntax.lbdef = imp
                         } in
                       [uu____3060] in
                     (false, uu____3057) in
                   (uu____3050, []) in
                 FStar_Syntax_Syntax.Sig_let uu____3043 in
               {
                 FStar_Syntax_Syntax.sigel = uu____3042;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___165_3041.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___165_3041.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___165_3041.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___165_3041.FStar_Syntax_Syntax.sigattrs)
               } in
             let uu____3077 = extract_sig g always_fail in
             (match uu____3077 with
              | (g1,mlm) ->
                  let uu____3096 =
                    FStar_Util.find_map quals
                      (fun uu___162_3101  ->
                         match uu___162_3101 with
                         | FStar_Syntax_Syntax.Discriminator l ->
                             FStar_Pervasives_Native.Some l
                         | uu____3105 -> FStar_Pervasives_Native.None) in
                  (match uu____3096 with
                   | FStar_Pervasives_Native.Some l ->
                       let uu____3113 =
                         let uu____3116 =
                           let uu____3117 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____3117 in
                         let uu____3118 =
                           let uu____3121 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l in
                           [uu____3121] in
                         uu____3116 :: uu____3118 in
                       (g1, uu____3113)
                   | uu____3124 ->
                       let uu____3127 =
                         FStar_Util.find_map quals
                           (fun uu___163_3133  ->
                              match uu___163_3133 with
                              | FStar_Syntax_Syntax.Projector (l,uu____3137)
                                  -> FStar_Pervasives_Native.Some l
                              | uu____3138 -> FStar_Pervasives_Native.None) in
                       (match uu____3127 with
                        | FStar_Pervasives_Native.Some uu____3145 -> (g1, [])
                        | uu____3148 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____3157 = FStar_Extraction_ML_Term.term_as_mlexpr g e in
           (match uu____3157 with
            | (ml_main,uu____3171,uu____3172) ->
                let uu____3173 =
                  let uu____3176 =
                    let uu____3177 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____3177 in
                  [uu____3176; FStar_Extraction_ML_Syntax.MLM_Top ml_main] in
                (g, uu____3173))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____3180 ->
           failwith "impossible -- removed by tc.fs"
       | FStar_Syntax_Syntax.Sig_assume uu____3187 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____3196 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____3199 -> (g, [])
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (if p = FStar_Syntax_Syntax.LightOff
            then FStar_Options.set_ml_ish ()
            else ();
            (g, [])))
let extract_iface:
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.modul -> env_t =
  fun g  ->
    fun m  ->
      let uu____3227 =
        FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____3227 FStar_Pervasives_Native.fst
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
      (let uu____3272 = FStar_Options.debug_any () in
       if uu____3272
       then
         let uu____3273 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
         FStar_Util.print1 "Extracting module %s\n" uu____3273
       else ());
      (let codegen_opt = FStar_Options.codegen () in
       let uu____3278 = FStar_Options.restore_cmd_line_options true in
       (match codegen_opt with
        | FStar_Pervasives_Native.Some "OCaml" ->
            FStar_Options.set_option "codegen" (FStar_Options.String "OCaml")
        | uu____3280 -> ());
       (let name =
          FStar_Extraction_ML_Syntax.mlpath_of_lident
            m.FStar_Syntax_Syntax.name in
        let g1 =
          let uu___166_3285 = g in
          let uu____3286 =
            FStar_TypeChecker_Env.set_current_module
              g.FStar_Extraction_ML_UEnv.tcenv m.FStar_Syntax_Syntax.name in
          {
            FStar_Extraction_ML_UEnv.tcenv = uu____3286;
            FStar_Extraction_ML_UEnv.gamma =
              (uu___166_3285.FStar_Extraction_ML_UEnv.gamma);
            FStar_Extraction_ML_UEnv.tydefs =
              (uu___166_3285.FStar_Extraction_ML_UEnv.tydefs);
            FStar_Extraction_ML_UEnv.type_names =
              (uu___166_3285.FStar_Extraction_ML_UEnv.type_names);
            FStar_Extraction_ML_UEnv.currentModule = name
          } in
        let uu____3287 =
          FStar_Util.fold_map extract_sig g1
            m.FStar_Syntax_Syntax.declarations in
        match uu____3287 with
        | (g2,sigs) ->
            let mlm = FStar_List.flatten sigs in
            let is_kremlin =
              let uu____3316 = FStar_Options.codegen () in
              match uu____3316 with
              | FStar_Pervasives_Native.Some "Kremlin" -> true
              | uu____3319 -> false in
            let uu____3322 =
              (((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
                 (is_kremlin ||
                    (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)))
                &&
                (FStar_Options.should_extract
                   (m.FStar_Syntax_Syntax.name).FStar_Ident.str) in
            if uu____3322
            then
              ((let uu____3330 =
                  FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
                FStar_Util.print1 "Extracted module %s\n" uu____3330);
               (g2,
                 [FStar_Extraction_ML_Syntax.MLLib
                    [(name, (FStar_Pervasives_Native.Some ([], mlm)),
                       (FStar_Extraction_ML_Syntax.MLLib []))]]))
            else (g2, [])))