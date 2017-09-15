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
        (FStar_Extraction_ML_UEnv.env,(Prims.string,Prims.int)
                                        FStar_Pervasives_Native.tuple2
                                        Prims.list)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bs  ->
      FStar_Util.fold_map
        (fun env1  ->
           fun uu____225  ->
             match uu____225 with
             | (bv,uu____239) ->
                 let uu____240 =
                   let uu____241 =
                     let uu____244 =
                       let uu____245 =
                         FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv in
                       FStar_Extraction_ML_Syntax.MLTY_Var uu____245 in
                     FStar_Pervasives_Native.Some uu____244 in
                   FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____241 in
                 let uu____246 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv in
                 (uu____240, uu____246)) env bs
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
              let uu____291 =
                let uu____292 = FStar_Syntax_Subst.compress def in
                FStar_All.pipe_right uu____292 FStar_Syntax_Util.unmeta in
              FStar_All.pipe_right uu____291 FStar_Syntax_Util.un_uinst in
            let def2 =
              match def1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_abs uu____294 ->
                  FStar_Extraction_ML_Term.normalize_abs def1
              | uu____311 -> def1 in
            let uu____312 =
              match def2.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____323) ->
                  FStar_Syntax_Subst.open_term bs body
              | uu____344 -> ([], def2) in
            match uu____312 with
            | (bs,body) ->
                let assumed =
                  FStar_Util.for_some
                    (fun uu___155_365  ->
                       match uu___155_365 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____366 -> false) quals in
                let uu____367 = binders_as_mlty_binders env bs in
                (match uu____367 with
                 | (env1,ml_bs) ->
                     let body1 =
                       let uu____399 =
                         FStar_Extraction_ML_Term.term_as_mlty env1 body in
                       FStar_All.pipe_right uu____399
                         (FStar_Extraction_ML_Util.eraseTypeDeep
                            (FStar_Extraction_ML_Util.udelta_unfold env1)) in
                     let mangled_projector =
                       let uu____403 =
                         FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___156_408  ->
                                 match uu___156_408 with
                                 | FStar_Syntax_Syntax.Projector uu____409 ->
                                     true
                                 | uu____414 -> false)) in
                       if uu____403
                       then
                         let mname = mangle_projector_lid lid in
                         FStar_Pervasives_Native.Some
                           ((mname.FStar_Ident.ident).FStar_Ident.idText)
                       else FStar_Pervasives_Native.None in
                     let attrs1 = extract_attrs attrs in
                     let td =
                       let uu____449 =
                         let uu____474 = lident_as_mlsymbol lid in
                         (assumed, uu____474, mangled_projector, ml_bs,
                           attrs1,
                           (FStar_Pervasives_Native.Some
                              (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1))) in
                       [uu____449] in
                     let def3 =
                       let uu____538 =
                         let uu____539 =
                           FStar_Extraction_ML_Util.mlloc_of_range
                             (FStar_Ident.range_of_lid lid) in
                         FStar_Extraction_ML_Syntax.MLM_Loc uu____539 in
                       [uu____538; FStar_Extraction_ML_Syntax.MLM_Ty td] in
                     let env2 =
                       let uu____541 =
                         FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___157_545  ->
                                 match uu___157_545 with
                                 | FStar_Syntax_Syntax.Assumption  -> true
                                 | FStar_Syntax_Syntax.New  -> true
                                 | uu____546 -> false)) in
                       if uu____541
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
    let uu____694 = FStar_Syntax_Print.lid_to_string i.iname in
    let uu____695 = FStar_Syntax_Print.binders_to_string " " i.iparams in
    let uu____696 = FStar_Syntax_Print.term_to_string i.ityp in
    let uu____697 =
      let uu____698 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let uu____709 = FStar_Syntax_Print.lid_to_string d.dname in
                let uu____710 =
                  let uu____711 = FStar_Syntax_Print.term_to_string d.dtyp in
                  Prims.strcat " : " uu____711 in
                Prims.strcat uu____709 uu____710)) in
      FStar_All.pipe_right uu____698 (FStar_String.concat "\n\t\t") in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____694 uu____695 uu____696
      uu____697
let bundle_as_inductive_families:
  'Auu____724 .
    FStar_Extraction_ML_UEnv.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'Auu____724 ->
          FStar_Syntax_Syntax.attribute Prims.list ->
            (FStar_Extraction_ML_UEnv.env,inductive_family Prims.list)
              FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun attrs  ->
          let uu____755 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun se  ->
                   match se.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,_us,bs,t,_mut_i,datas) ->
                       let uu____802 = FStar_Syntax_Subst.open_term bs t in
                       (match uu____802 with
                        | (bs1,t1) ->
                            let datas1 =
                              FStar_All.pipe_right ses
                                (FStar_List.collect
                                   (fun se1  ->
                                      match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_datacon
                                          (d,uu____841,t2,l',nparams,uu____845)
                                          when FStar_Ident.lid_equals l l' ->
                                          let uu____850 =
                                            FStar_Syntax_Util.arrow_formals
                                              t2 in
                                          (match uu____850 with
                                           | (bs',body) ->
                                               let uu____883 =
                                                 FStar_Util.first_N
                                                   (FStar_List.length bs1)
                                                   bs' in
                                               (match uu____883 with
                                                | (bs_params,rest) ->
                                                    let subst1 =
                                                      FStar_List.map2
                                                        (fun uu____954  ->
                                                           fun uu____955  ->
                                                             match (uu____954,
                                                                    uu____955)
                                                             with
                                                             | ((b',uu____973),
                                                                (b,uu____975))
                                                                 ->
                                                                 let uu____984
                                                                   =
                                                                   let uu____991
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b in
                                                                   (b',
                                                                    uu____991) in
                                                                 FStar_Syntax_Syntax.NT
                                                                   uu____984)
                                                        bs_params bs1 in
                                                    let t3 =
                                                      let uu____993 =
                                                        let uu____996 =
                                                          FStar_Syntax_Syntax.mk_Total
                                                            body in
                                                        FStar_Syntax_Util.arrow
                                                          rest uu____996 in
                                                      FStar_All.pipe_right
                                                        uu____993
                                                        (FStar_Syntax_Subst.subst
                                                           subst1) in
                                                    [{ dname = d; dtyp = t3 }]))
                                      | uu____1001 -> [])) in
                            let attrs1 =
                              extract_attrs
                                (FStar_List.append
                                   se.FStar_Syntax_Syntax.sigattrs attrs) in
                            let env2 =
                              let uu____1006 =
                                FStar_Syntax_Syntax.lid_as_fv l
                                  FStar_Syntax_Syntax.Delta_constant
                                  FStar_Pervasives_Native.None in
                              FStar_Extraction_ML_UEnv.extend_type_name env1
                                uu____1006 in
                            (env2,
                              [{
                                 iname = l;
                                 iparams = bs1;
                                 ityp = t1;
                                 idatas = datas1;
                                 iquals = (se.FStar_Syntax_Syntax.sigquals);
                                 iattrs = attrs1
                               }]))
                   | uu____1009 -> (env1, [])) env ses in
          match uu____755 with
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
          let uu____1095 =
            FStar_Extraction_ML_Term.term_as_mlty env1 ctor.dtyp in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env1) uu____1095 in
        let steps =
          [FStar_TypeChecker_Normalize.Inlining;
          FStar_TypeChecker_Normalize.UnfoldUntil
            FStar_Syntax_Syntax.Delta_constant;
          FStar_TypeChecker_Normalize.EraseUniverses;
          FStar_TypeChecker_Normalize.AllowUnboundUniverses] in
        let names1 =
          let uu____1102 =
            let uu____1103 =
              let uu____1106 =
                FStar_TypeChecker_Normalize.normalize steps
                  env1.FStar_Extraction_ML_UEnv.tcenv ctor.dtyp in
              FStar_Syntax_Subst.compress uu____1106 in
            uu____1103.FStar_Syntax_Syntax.n in
          match uu____1102 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,uu____1110) ->
              FStar_List.map
                (fun uu____1136  ->
                   match uu____1136 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____1142;
                        FStar_Syntax_Syntax.sort = uu____1143;_},uu____1144)
                       -> ppname.FStar_Ident.idText) bs
          | uu____1147 -> [] in
        let tys = (ml_tyvars, mlt) in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp in
        let uu____1166 =
          let uu____1167 =
            FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false in
          FStar_Pervasives_Native.fst uu____1167 in
        let uu____1172 =
          let uu____1183 = lident_as_mlsymbol ctor.dname in
          let uu____1184 =
            let uu____1191 = FStar_Extraction_ML_Util.argTypes mlt in
            FStar_List.zip names1 uu____1191 in
          (uu____1183, uu____1184) in
        (uu____1166, uu____1172) in
      let extract_one_family env1 ind =
        let uu____1243 = binders_as_mlty_binders env1 ind.iparams in
        match uu____1243 with
        | (env2,vars) ->
            let uu____1294 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor vars) env2) in
            (match uu____1294 with
             | (env3,ctors) ->
                 let uu____1391 = FStar_Syntax_Util.arrow_formals ind.ityp in
                 (match uu____1391 with
                  | (indices,uu____1431) ->
                      let ml_params =
                        let uu____1455 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____1486  ->
                                    let uu____1491 =
                                      let uu____1492 =
                                        FStar_Util.string_of_int i in
                                      Prims.strcat "'dummyV" uu____1492 in
                                    (uu____1491, (Prims.parse_int "0")))) in
                        FStar_List.append vars uu____1455 in
                      let tbody =
                        let uu____1498 =
                          FStar_Util.find_opt
                            (fun uu___158_1503  ->
                               match uu___158_1503 with
                               | FStar_Syntax_Syntax.RecordType uu____1504 ->
                                   true
                               | uu____1513 -> false) ind.iquals in
                        match uu____1498 with
                        | FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____1524 = FStar_List.hd ctors in
                            (match uu____1524 with
                             | (uu____1545,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id  ->
                                        fun uu____1584  ->
                                          match uu____1584 with
                                          | (uu____1593,ty) ->
                                              let lid =
                                                FStar_Ident.lid_of_ids
                                                  (FStar_List.append ns [id]) in
                                              let uu____1596 =
                                                lident_as_mlsymbol lid in
                                              (uu____1596, ty)) ids c_ty in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____1597 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors in
                      let uu____1600 =
                        let uu____1623 = lident_as_mlsymbol ind.iname in
                        (false, uu____1623, FStar_Pervasives_Native.None,
                          ml_params, (ind.iattrs),
                          (FStar_Pervasives_Native.Some tbody)) in
                      (env3, uu____1600))) in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____1665,t,uu____1667,uu____1668,uu____1669);
            FStar_Syntax_Syntax.sigrng = uu____1670;
            FStar_Syntax_Syntax.sigquals = uu____1671;
            FStar_Syntax_Syntax.sigmeta = uu____1672;
            FStar_Syntax_Syntax.sigattrs = uu____1673;_}::[],uu____1674),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____1691 = extract_ctor [] env { dname = l; dtyp = t } in
          (match uu____1691 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____1741),quals) ->
          let uu____1755 =
            bundle_as_inductive_families env ses quals
              se.FStar_Syntax_Syntax.sigattrs in
          (match uu____1755 with
           | (env1,ifams) ->
               let uu____1776 =
                 FStar_Util.fold_map extract_one_family env1 ifams in
               (match uu____1776 with
                | (env2,td) -> (env2, [FStar_Extraction_ML_Syntax.MLM_Ty td])))
      | uu____1885 -> failwith "Unexpected signature element"
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
           let uu____1922 = FStar_Syntax_Print.sigelt_to_string se in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____1922);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____1929 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____1938 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____1955 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
           ->
           let extend_env g1 lid ml_name tm tysc =
             let uu____1993 =
               let uu____1998 =
                 FStar_Syntax_Syntax.lid_as_fv lid
                   FStar_Syntax_Syntax.Delta_equational
                   FStar_Pervasives_Native.None in
               FStar_Extraction_ML_UEnv.extend_fv' g1 uu____1998 ml_name tysc
                 false false in
             match uu____1993 with
             | (g2,mangled_name) ->
                 ((let uu____2006 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          g2.FStar_Extraction_ML_UEnv.tcenv)
                       (FStar_Options.Other "ExtractionReify") in
                   if uu____2006
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
             (let uu____2022 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify") in
              if uu____2022
              then
                let uu____2023 = FStar_Syntax_Print.term_to_string tm in
                FStar_Util.print1 "extract_fv term: %s\n" uu____2023
              else ());
             (let uu____2025 =
                let uu____2026 = FStar_Syntax_Subst.compress tm in
                uu____2026.FStar_Syntax_Syntax.n in
              match uu____2025 with
              | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____2034) ->
                  extract_fv tm1
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let mlp =
                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  let uu____2041 =
                    let uu____2050 = FStar_Extraction_ML_UEnv.lookup_fv g fv in
                    FStar_All.pipe_left FStar_Util.right uu____2050 in
                  (match uu____2041 with
                   | (uu____2107,uu____2108,tysc,uu____2110) ->
                       let uu____2111 =
                         FStar_All.pipe_left
                           (FStar_Extraction_ML_Syntax.with_ty
                              FStar_Extraction_ML_Syntax.MLTY_Top)
                           (FStar_Extraction_ML_Syntax.MLE_Name mlp) in
                       (uu____2111, tysc))
              | uu____2112 -> failwith "Not an fv") in
           let extract_action g1 a =
             (let uu____2138 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g1.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify") in
              if uu____2138
              then
                let uu____2139 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_typ in
                let uu____2140 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_defn in
                FStar_Util.print2 "Action type %s and term %s\n" uu____2139
                  uu____2140
              else ());
             (let uu____2142 = FStar_Extraction_ML_UEnv.action_name ed a in
              match uu____2142 with
              | (a_nm,a_lid) ->
                  let lbname =
                    let uu____2158 =
                      FStar_Syntax_Syntax.new_bv
                        (FStar_Pervasives_Native.Some
                           ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                        FStar_Syntax_Syntax.tun in
                    FStar_Util.Inl uu____2158 in
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
                  let uu____2184 =
                    FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb in
                  (match uu____2184 with
                   | (a_let,uu____2196,ty) ->
                       ((let uu____2199 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug
                                g1.FStar_Extraction_ML_UEnv.tcenv)
                             (FStar_Options.Other "ExtractionReify") in
                         if uu____2199
                         then
                           let uu____2200 =
                             FStar_Extraction_ML_Code.string_of_mlexpr a_nm
                               a_let in
                           FStar_Util.print1 "Extracted action term: %s\n"
                             uu____2200
                         else ());
                        (let uu____2202 =
                           match a_let.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_Let
                               ((uu____2211,uu____2212,mllb::[]),uu____2214)
                               ->
                               (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                                with
                                | FStar_Pervasives_Native.Some tysc ->
                                    ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                      tysc)
                                | FStar_Pervasives_Native.None  ->
                                    failwith "No type scheme")
                           | uu____2234 -> failwith "Impossible" in
                         match uu____2202 with
                         | (exp,tysc) ->
                             ((let uu____2246 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug
                                      g1.FStar_Extraction_ML_UEnv.tcenv)
                                   (FStar_Options.Other "ExtractionReify") in
                               if uu____2246
                               then
                                 ((let uu____2248 =
                                     FStar_Extraction_ML_Code.string_of_mlty
                                       a_nm
                                       (FStar_Pervasives_Native.snd tysc) in
                                   FStar_Util.print1
                                     "Extracted action type: %s\n" uu____2248);
                                  FStar_List.iter
                                    (fun x  ->
                                       FStar_Util.print1 "and binders: %s\n"
                                         (FStar_Pervasives_Native.fst x))
                                    (FStar_Pervasives_Native.fst tysc))
                               else ());
                              extend_env g1 a_lid a_nm exp tysc))))) in
           let uu____2260 =
             let uu____2265 =
               extract_fv
                 (FStar_Pervasives_Native.snd
                    ed.FStar_Syntax_Syntax.return_repr) in
             match uu____2265 with
             | (return_tm,ty_sc) ->
                 let uu____2278 =
                   FStar_Extraction_ML_UEnv.monad_op_name ed "return" in
                 (match uu____2278 with
                  | (return_nm,return_lid) ->
                      extend_env g return_lid return_nm return_tm ty_sc) in
           (match uu____2260 with
            | (g1,return_decl) ->
                let uu____2297 =
                  let uu____2302 =
                    extract_fv
                      (FStar_Pervasives_Native.snd
                         ed.FStar_Syntax_Syntax.bind_repr) in
                  match uu____2302 with
                  | (bind_tm,ty_sc) ->
                      let uu____2315 =
                        FStar_Extraction_ML_UEnv.monad_op_name ed "bind" in
                      (match uu____2315 with
                       | (bind_nm,bind_lid) ->
                           extend_env g1 bind_lid bind_nm bind_tm ty_sc) in
                (match uu____2297 with
                 | (g2,bind_decl) ->
                     let uu____2334 =
                       FStar_Util.fold_map extract_action g2
                         ed.FStar_Syntax_Syntax.actions in
                     (match uu____2334 with
                      | (g3,actions) ->
                          (g3,
                            (FStar_List.append [return_decl; bind_decl]
                               actions)))))
       | FStar_Syntax_Syntax.Sig_new_effect uu____2355 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____2359,t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let attrs = se.FStar_Syntax_Syntax.sigattrs in
           let uu____2367 =
             let uu____2368 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___159_2372  ->
                       match uu___159_2372 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____2373 -> false)) in
             Prims.op_Negation uu____2368 in
           if uu____2367
           then (g, [])
           else
             (let uu____2383 = FStar_Syntax_Util.arrow_formals t in
              match uu____2383 with
              | (bs,uu____2403) ->
                  let fv =
                    FStar_Syntax_Syntax.lid_as_fv lid
                      FStar_Syntax_Syntax.Delta_constant
                      FStar_Pervasives_Native.None in
                  let uu____2421 =
                    FStar_Syntax_Util.abs bs FStar_Syntax_Syntax.t_unit
                      FStar_Pervasives_Native.None in
                  extract_typ_abbrev g fv quals attrs uu____2421)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____2423) when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____2439 =
             let uu____2448 =
               FStar_TypeChecker_Env.open_universes_in
                 g.FStar_Extraction_ML_UEnv.tcenv
                 lb.FStar_Syntax_Syntax.lbunivs
                 [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp] in
             match uu____2448 with
             | (tcenv,uu____2472,def_typ) ->
                 let uu____2478 = as_pair def_typ in (tcenv, uu____2478) in
           (match uu____2439 with
            | (tcenv,(lbdef,lbtyp)) ->
                let lbtyp1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.UnfoldUntil
                      FStar_Syntax_Syntax.Delta_constant] tcenv lbtyp in
                let lbdef1 =
                  FStar_TypeChecker_Normalize.eta_expand_with_type tcenv
                    lbdef lbtyp1 in
                let uu____2502 =
                  FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                extract_typ_abbrev g uu____2502 quals
                  se.FStar_Syntax_Syntax.sigattrs lbdef1)
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____2504) ->
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
               | FStar_Syntax_Syntax.Tm_uinst (h',uu____2531) ->
                   let uu____2536 =
                     let uu____2537 = FStar_Syntax_Subst.compress h' in
                     uu____2537.FStar_Syntax_Syntax.n in
                   (match uu____2536 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.tactic_lid
                        ->
                        let uu____2541 =
                          let uu____2542 =
                            FStar_Extraction_ML_Syntax.string_of_mlpath
                              g.FStar_Extraction_ML_UEnv.currentModule in
                          FStar_Util.starts_with uu____2542 "FStar.Tactics" in
                        Prims.op_Negation uu____2541
                    | uu____2543 -> false)
               | uu____2544 -> false in
             let mk_registration tac_lid assm_lid t bs =
               let h =
                 let uu____2573 =
                   let uu____2574 =
                     let uu____2575 =
                       FStar_Ident.lid_of_str
                         "FStar_Tactics_Native.register_tactic" in
                     FStar_Extraction_ML_Syntax.mlpath_of_lident uu____2575 in
                   FStar_Extraction_ML_Syntax.MLE_Name uu____2574 in
                 FStar_All.pipe_left
                   (FStar_Extraction_ML_Syntax.with_ty
                      FStar_Extraction_ML_Syntax.MLTY_Top) uu____2573 in
               let lid_arg =
                 let uu____2577 =
                   let uu____2578 = FStar_Ident.string_of_lid assm_lid in
                   FStar_Extraction_ML_Syntax.MLC_String uu____2578 in
                 FStar_Extraction_ML_Syntax.MLE_Const uu____2577 in
               let tac_arity = FStar_List.length bs in
               let arity =
                 let uu____2585 =
                   let uu____2586 =
                     let uu____2587 =
                       FStar_Util.string_of_int
                         (tac_arity + (Prims.parse_int "1")) in
                     FStar_Ident.lid_of_str uu____2587 in
                   FStar_Extraction_ML_Syntax.mlpath_of_lident uu____2586 in
                 FStar_Extraction_ML_Syntax.MLE_Name uu____2585 in
               let uu____2594 =
                 FStar_Extraction_ML_Util.mk_interpretation_fun tac_lid
                   lid_arg t bs in
               match uu____2594 with
               | FStar_Pervasives_Native.Some tac_interpretation ->
                   let app =
                     let uu____2601 =
                       let uu____2602 =
                         let uu____2609 =
                           FStar_List.map
                             (FStar_Extraction_ML_Syntax.with_ty
                                FStar_Extraction_ML_Syntax.MLTY_Top)
                             [lid_arg; arity; tac_interpretation] in
                         (h, uu____2609) in
                       FStar_Extraction_ML_Syntax.MLE_App uu____2602 in
                     FStar_All.pipe_left
                       (FStar_Extraction_ML_Syntax.with_ty
                          FStar_Extraction_ML_Syntax.MLTY_Top) uu____2601 in
                   [FStar_Extraction_ML_Syntax.MLM_Top app]
               | FStar_Pervasives_Native.None  -> [] in
             match FStar_Pervasives_Native.snd lbs with
             | hd1::[] ->
                 let uu____2619 =
                   FStar_Syntax_Util.arrow_formals_comp
                     hd1.FStar_Syntax_Syntax.lbtyp in
                 (match uu____2619 with
                  | (bs,comp) ->
                      let t = FStar_Syntax_Util.comp_result comp in
                      let uu____2649 =
                        let uu____2650 = FStar_Syntax_Subst.compress t in
                        uu____2650.FStar_Syntax_Syntax.n in
                      (match uu____2649 with
                       | FStar_Syntax_Syntax.Tm_app (h,args) ->
                           let h1 = FStar_Syntax_Subst.compress h in
                           let tac_lid =
                             let uu____2679 =
                               let uu____2682 =
                                 FStar_Util.right
                                   hd1.FStar_Syntax_Syntax.lbname in
                               uu____2682.FStar_Syntax_Syntax.fv_name in
                             uu____2679.FStar_Syntax_Syntax.v in
                           let assm_lid =
                             let uu____2684 =
                               FStar_All.pipe_left FStar_Ident.id_of_text
                                 (Prims.strcat "__"
                                    (tac_lid.FStar_Ident.ident).FStar_Ident.idText) in
                             FStar_Ident.lid_of_ns_and_id
                               tac_lid.FStar_Ident.ns uu____2684 in
                           let uu____2685 = is_tactic_decl assm_lid h1 in
                           if uu____2685
                           then
                             let uu____2688 =
                               let uu____2689 = FStar_List.hd args in
                               FStar_Pervasives_Native.fst uu____2689 in
                             mk_registration tac_lid assm_lid uu____2688 bs
                           else []
                       | uu____2705 -> []))
             | uu____2706 -> [] in
           let uu____2709 = FStar_Extraction_ML_Term.term_as_mlexpr g elet in
           (match uu____2709 with
            | (ml_let,uu____2723,uu____2724) ->
                (match ml_let.FStar_Extraction_ML_Syntax.expr with
                 | FStar_Extraction_ML_Syntax.MLE_Let
                     ((flavor,uu____2732,bindings),uu____2734) ->
                     let uu____2747 =
                       FStar_List.fold_left2
                         (fun uu____2774  ->
                            fun ml_lb  ->
                              fun uu____2776  ->
                                match (uu____2774, uu____2776) with
                                | ((env,ml_lbs),{
                                                  FStar_Syntax_Syntax.lbname
                                                    = lbname;
                                                  FStar_Syntax_Syntax.lbunivs
                                                    = uu____2798;
                                                  FStar_Syntax_Syntax.lbtyp =
                                                    t;
                                                  FStar_Syntax_Syntax.lbeff =
                                                    uu____2800;
                                                  FStar_Syntax_Syntax.lbdef =
                                                    uu____2801;_})
                                    ->
                                    let lb_lid =
                                      let uu____2823 =
                                        let uu____2826 =
                                          FStar_Util.right lbname in
                                        uu____2826.FStar_Syntax_Syntax.fv_name in
                                      uu____2823.FStar_Syntax_Syntax.v in
                                    let uu____2827 =
                                      let uu____2832 =
                                        FStar_All.pipe_right quals
                                          (FStar_Util.for_some
                                             (fun uu___160_2837  ->
                                                match uu___160_2837 with
                                                | FStar_Syntax_Syntax.Projector
                                                    uu____2838 -> true
                                                | uu____2843 -> false)) in
                                      if uu____2832
                                      then
                                        let mname =
                                          let uu____2849 =
                                            mangle_projector_lid lb_lid in
                                          FStar_All.pipe_right uu____2849
                                            FStar_Extraction_ML_Syntax.mlpath_of_lident in
                                        let uu____2850 =
                                          let uu____2855 =
                                            FStar_Util.right lbname in
                                          let uu____2856 =
                                            FStar_Util.must
                                              ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc in
                                          FStar_Extraction_ML_UEnv.extend_fv'
                                            env uu____2855 mname uu____2856
                                            ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                            false in
                                        match uu____2850 with
                                        | (env1,uu____2862) ->
                                            (env1,
                                              (let uu___165_2864 = ml_lb in
                                               {
                                                 FStar_Extraction_ML_Syntax.mllb_name
                                                   =
                                                   ((FStar_Pervasives_Native.snd
                                                       mname),
                                                     (Prims.parse_int "0"));
                                                 FStar_Extraction_ML_Syntax.mllb_tysc
                                                   =
                                                   (uu___165_2864.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                 FStar_Extraction_ML_Syntax.mllb_add_unit
                                                   =
                                                   (uu___165_2864.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                 FStar_Extraction_ML_Syntax.mllb_def
                                                   =
                                                   (uu___165_2864.FStar_Extraction_ML_Syntax.mllb_def);
                                                 FStar_Extraction_ML_Syntax.print_typ
                                                   =
                                                   (uu___165_2864.FStar_Extraction_ML_Syntax.print_typ)
                                               }))
                                      else
                                        (let uu____2868 =
                                           let uu____2869 =
                                             let uu____2874 =
                                               FStar_Util.must
                                                 ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc in
                                             FStar_Extraction_ML_UEnv.extend_lb
                                               env lbname t uu____2874
                                               ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                               false in
                                           FStar_All.pipe_left
                                             FStar_Pervasives_Native.fst
                                             uu____2869 in
                                         (uu____2868, ml_lb)) in
                                    (match uu____2827 with
                                     | (g1,ml_lb1) ->
                                         (g1, (ml_lb1 :: ml_lbs)))) (g, [])
                         bindings (FStar_Pervasives_Native.snd lbs) in
                     (match uu____2747 with
                      | (g1,ml_lbs') ->
                          let flags =
                            FStar_List.choose
                              (fun uu___161_2909  ->
                                 match uu___161_2909 with
                                 | FStar_Syntax_Syntax.Assumption  ->
                                     FStar_Pervasives_Native.Some
                                       FStar_Extraction_ML_Syntax.Assumed
                                 | FStar_Syntax_Syntax.Private  ->
                                     FStar_Pervasives_Native.Some
                                       FStar_Extraction_ML_Syntax.Private
                                 | FStar_Syntax_Syntax.NoExtract  ->
                                     FStar_Pervasives_Native.Some
                                       FStar_Extraction_ML_Syntax.NoExtract
                                 | uu____2912 -> FStar_Pervasives_Native.None)
                              quals in
                          let flags' =
                            FStar_List.choose
                              (fun uu___162_2923  ->
                                 match uu___162_2923 with
                                 | {
                                     FStar_Syntax_Syntax.n =
                                       FStar_Syntax_Syntax.Tm_constant
                                       (FStar_Const.Const_string
                                       (s,uu____2929));
                                     FStar_Syntax_Syntax.pos = uu____2930;
                                     FStar_Syntax_Syntax.vars = uu____2931;_}
                                     ->
                                     FStar_Pervasives_Native.Some
                                       (FStar_Extraction_ML_Syntax.Attribute
                                          s)
                                 | uu____2934 ->
                                     (FStar_Util.print_warning
                                        "Warning: unrecognized, non-string attribute, bother protz for a better error message";
                                      FStar_Pervasives_Native.None)) attrs in
                          let uu____2938 =
                            let uu____2941 =
                              let uu____2944 =
                                let uu____2945 =
                                  FStar_Extraction_ML_Util.mlloc_of_range
                                    se.FStar_Syntax_Syntax.sigrng in
                                FStar_Extraction_ML_Syntax.MLM_Loc uu____2945 in
                              [uu____2944;
                              FStar_Extraction_ML_Syntax.MLM_Let
                                (flavor, (FStar_List.append flags flags'),
                                  (FStar_List.rev ml_lbs'))] in
                            FStar_List.append uu____2941
                              tactic_registration_decl in
                          (g1, uu____2938))
                 | uu____2952 ->
                     let uu____2953 =
                       let uu____2954 =
                         FStar_Extraction_ML_Code.string_of_mlexpr
                           g.FStar_Extraction_ML_UEnv.currentModule ml_let in
                       FStar_Util.format1
                         "Impossible: Translated a let to a non-let: %s"
                         uu____2954 in
                     failwith uu____2953))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____2962,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____2967 =
             FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption) in
           if uu____2967
           then
             let always_fail =
               let imp =
                 let uu____2978 = FStar_Syntax_Util.arrow_formals t in
                 match uu____2978 with
                 | ([],t1) ->
                     let b =
                       let uu____3007 =
                         FStar_Syntax_Syntax.gen_bv "_"
                           FStar_Pervasives_Native.None t1 in
                       FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                         uu____3007 in
                     let uu____3008 = fail_exp lid t1 in
                     FStar_Syntax_Util.abs [b] uu____3008
                       FStar_Pervasives_Native.None
                 | (bs,t1) ->
                     let uu____3027 = fail_exp lid t1 in
                     FStar_Syntax_Util.abs bs uu____3027
                       FStar_Pervasives_Native.None in
               let uu___166_3028 = se in
               let uu____3029 =
                 let uu____3030 =
                   let uu____3037 =
                     let uu____3044 =
                       let uu____3047 =
                         let uu____3048 =
                           let uu____3053 =
                             FStar_Syntax_Syntax.lid_as_fv lid
                               FStar_Syntax_Syntax.Delta_constant
                               FStar_Pervasives_Native.None in
                           FStar_Util.Inr uu____3053 in
                         {
                           FStar_Syntax_Syntax.lbname = uu____3048;
                           FStar_Syntax_Syntax.lbunivs = [];
                           FStar_Syntax_Syntax.lbtyp = t;
                           FStar_Syntax_Syntax.lbeff =
                             FStar_Parser_Const.effect_ML_lid;
                           FStar_Syntax_Syntax.lbdef = imp
                         } in
                       [uu____3047] in
                     (false, uu____3044) in
                   (uu____3037, []) in
                 FStar_Syntax_Syntax.Sig_let uu____3030 in
               {
                 FStar_Syntax_Syntax.sigel = uu____3029;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___166_3028.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___166_3028.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___166_3028.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___166_3028.FStar_Syntax_Syntax.sigattrs)
               } in
             let uu____3064 = extract_sig g always_fail in
             (match uu____3064 with
              | (g1,mlm) ->
                  let uu____3083 =
                    FStar_Util.find_map quals
                      (fun uu___163_3088  ->
                         match uu___163_3088 with
                         | FStar_Syntax_Syntax.Discriminator l ->
                             FStar_Pervasives_Native.Some l
                         | uu____3092 -> FStar_Pervasives_Native.None) in
                  (match uu____3083 with
                   | FStar_Pervasives_Native.Some l ->
                       let uu____3100 =
                         let uu____3103 =
                           let uu____3104 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____3104 in
                         let uu____3105 =
                           let uu____3108 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l in
                           [uu____3108] in
                         uu____3103 :: uu____3105 in
                       (g1, uu____3100)
                   | uu____3111 ->
                       let uu____3114 =
                         FStar_Util.find_map quals
                           (fun uu___164_3120  ->
                              match uu___164_3120 with
                              | FStar_Syntax_Syntax.Projector (l,uu____3124)
                                  -> FStar_Pervasives_Native.Some l
                              | uu____3125 -> FStar_Pervasives_Native.None) in
                       (match uu____3114 with
                        | FStar_Pervasives_Native.Some uu____3132 -> (g1, [])
                        | uu____3135 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____3144 = FStar_Extraction_ML_Term.term_as_mlexpr g e in
           (match uu____3144 with
            | (ml_main,uu____3158,uu____3159) ->
                let uu____3160 =
                  let uu____3163 =
                    let uu____3164 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____3164 in
                  [uu____3163; FStar_Extraction_ML_Syntax.MLM_Top ml_main] in
                (g, uu____3160))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____3167 ->
           failwith "impossible -- removed by tc.fs"
       | FStar_Syntax_Syntax.Sig_assume uu____3174 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____3183 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____3186 -> (g, [])
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (if p = FStar_Syntax_Syntax.LightOff
            then FStar_Options.set_ml_ish ()
            else ();
            (g, [])))
let extract_iface:
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.modul -> env_t =
  fun g  ->
    fun m  ->
      let uu____3214 =
        FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____3214 FStar_Pervasives_Native.fst
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
      (let uu____3259 = FStar_Options.debug_any () in
       if uu____3259
       then
         let uu____3260 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
         FStar_Util.print1 "Extracting module %s\n" uu____3260
       else ());
      (let codegen_opt = FStar_Options.codegen () in
       let uu____3265 = FStar_Options.restore_cmd_line_options true in
       (match codegen_opt with
        | FStar_Pervasives_Native.Some "OCaml" ->
            FStar_Options.set_option "codegen" (FStar_Options.String "OCaml")
        | uu____3267 -> ());
       (let name =
          FStar_Extraction_ML_Syntax.mlpath_of_lident
            m.FStar_Syntax_Syntax.name in
        let g1 =
          let uu___167_3272 = g in
          let uu____3273 =
            FStar_TypeChecker_Env.set_current_module
              g.FStar_Extraction_ML_UEnv.tcenv m.FStar_Syntax_Syntax.name in
          {
            FStar_Extraction_ML_UEnv.tcenv = uu____3273;
            FStar_Extraction_ML_UEnv.gamma =
              (uu___167_3272.FStar_Extraction_ML_UEnv.gamma);
            FStar_Extraction_ML_UEnv.tydefs =
              (uu___167_3272.FStar_Extraction_ML_UEnv.tydefs);
            FStar_Extraction_ML_UEnv.type_names =
              (uu___167_3272.FStar_Extraction_ML_UEnv.type_names);
            FStar_Extraction_ML_UEnv.currentModule = name
          } in
        let uu____3274 =
          FStar_Util.fold_map extract_sig g1
            m.FStar_Syntax_Syntax.declarations in
        match uu____3274 with
        | (g2,sigs) ->
            let mlm = FStar_List.flatten sigs in
            let is_kremlin =
              let uu____3303 = FStar_Options.codegen () in
              match uu____3303 with
              | FStar_Pervasives_Native.Some "Kremlin" -> true
              | uu____3306 -> false in
            let uu____3309 =
              (((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
                 (is_kremlin ||
                    (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)))
                &&
                (FStar_Options.should_extract
                   (m.FStar_Syntax_Syntax.name).FStar_Ident.str) in
            if uu____3309
            then
              ((let uu____3317 =
                  FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
                FStar_Util.print1 "Extracted module %s\n" uu____3317);
               (g2,
                 [FStar_Extraction_ML_Syntax.MLLib
                    [(name, (FStar_Pervasives_Native.Some ([], mlm)),
                       (FStar_Extraction_ML_Syntax.MLLib []))]]))
            else (g2, [])))