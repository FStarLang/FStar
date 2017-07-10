open Prims
let fail_exp lid t =
  let uu____18 =
    let uu____21 =
      let uu____22 =
        let uu____32 =
          FStar_Syntax_Syntax.fvar FStar_Parser_Const.failwith_lid
            FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None in
        let uu____33 =
          let uu____35 = FStar_Syntax_Syntax.iarg t in
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
                              FStar_Syntax_Print.lid_to_string lid in
                            Prims.strcat "Not yet implemented:" uu____51 in
                          FStar_Bytes.string_as_unicode_bytes uu____50 in
                        (uu____49, FStar_Range.dummyRange) in
                      FStar_Const.Const_string uu____45 in
                    FStar_Syntax_Syntax.Tm_constant uu____44 in
                  FStar_Syntax_Syntax.mk uu____43 in
                uu____40 FStar_Pervasives_Native.None FStar_Range.dummyRange in
              FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____39 in
            [uu____38] in
          uu____35 :: uu____36 in
        (uu____32, uu____33) in
      FStar_Syntax_Syntax.Tm_app uu____22 in
    FStar_Syntax_Syntax.mk uu____21 in
  uu____18 FStar_Pervasives_Native.None FStar_Range.dummyRange
let mangle_projector_lid: FStar_Ident.lident -> FStar_Ident.lident =
  fun x  -> x
let lident_as_mlsymbol: FStar_Ident.lident -> Prims.string =
  fun id  -> (id.FStar_Ident.ident).FStar_Ident.idText
let as_pair uu___147_88 =
  match uu___147_88 with
  | a::b::[] -> (a, b)
  | uu____92 -> failwith "Expected a list with 2 elements"
let rec extract_attr:
  FStar_Syntax_Syntax.term ->
    FStar_Extraction_ML_Syntax.tyattr FStar_Pervasives_Native.option
  =
  fun x  ->
    let uu____101 = FStar_Syntax_Subst.compress x in
    match uu____101 with
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
        FStar_Syntax_Syntax.tk = uu____104;
        FStar_Syntax_Syntax.pos = uu____105;_} when
        let uu____107 =
          let uu____108 = FStar_Syntax_Syntax.lid_of_fv fv in
          FStar_Ident.string_of_lid uu____108 in
        uu____107 = "FStar.Pervasives.PpxDerivingShow" ->
        FStar_Pervasives_Native.Some
          FStar_Extraction_ML_Syntax.PpxDerivingShow
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.tk = uu____110;
             FStar_Syntax_Syntax.pos = uu____111;_},({
                                                       FStar_Syntax_Syntax.n
                                                         =
                                                         FStar_Syntax_Syntax.Tm_constant
                                                         (FStar_Const.Const_string
                                                         (data,uu____113));
                                                       FStar_Syntax_Syntax.tk
                                                         = uu____114;
                                                       FStar_Syntax_Syntax.pos
                                                         = uu____115;_},uu____116)::[]);
        FStar_Syntax_Syntax.tk = uu____117;
        FStar_Syntax_Syntax.pos = uu____118;_} when
        let uu____141 =
          let uu____142 = FStar_Syntax_Syntax.lid_of_fv fv in
          FStar_Ident.string_of_lid uu____142 in
        uu____141 = "FStar.Pervasives.PpxDerivingShowConstant" ->
        FStar_Pervasives_Native.Some
          (FStar_Extraction_ML_Syntax.PpxDerivingShowConstant
             (FStar_Util.string_of_unicode data))
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_meta (x1,uu____144);
        FStar_Syntax_Syntax.tk = uu____145;
        FStar_Syntax_Syntax.pos = uu____146;_} -> extract_attr x1
    | a -> FStar_Pervasives_Native.None
let extract_attrs:
  FStar_Syntax_Syntax.term Prims.list ->
    FStar_Extraction_ML_Syntax.tyattr Prims.list
  = fun attrs  -> FStar_List.choose extract_attr attrs
let binders_as_mlty_binders env bs =
  FStar_Util.fold_map
    (fun env1  ->
       fun uu____197  ->
         match uu____197 with
         | (bv,uu____205) ->
             let uu____206 =
               let uu____207 =
                 let uu____209 =
                   let uu____210 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv in
                   FStar_Extraction_ML_Syntax.MLTY_Var uu____210 in
                 FStar_Pervasives_Native.Some uu____209 in
               FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____207 in
             let uu____211 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv in
             (uu____206, uu____211)) env bs
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
              let uu____245 =
                let uu____246 = FStar_Syntax_Subst.compress def in
                FStar_All.pipe_right uu____246 FStar_Syntax_Util.unmeta in
              FStar_All.pipe_right uu____245 FStar_Syntax_Util.un_uinst in
            let def2 =
              match def1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_abs uu____248 ->
                  FStar_Extraction_ML_Term.normalize_abs def1
              | uu____258 -> def1 in
            let uu____259 =
              match def2.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____266) ->
                  FStar_Syntax_Subst.open_term bs body
              | uu____279 -> ([], def2) in
            match uu____259 with
            | (bs,body) ->
                let assumed =
                  FStar_Util.for_some
                    (fun uu___148_292  ->
                       match uu___148_292 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____293 -> false) quals in
                let uu____294 = binders_as_mlty_binders env bs in
                (match uu____294 with
                 | (env1,ml_bs) ->
                     let body1 =
                       let uu____312 =
                         FStar_Extraction_ML_Term.term_as_mlty env1 body in
                       FStar_All.pipe_right uu____312
                         (FStar_Extraction_ML_Util.eraseTypeDeep
                            (FStar_Extraction_ML_Util.udelta_unfold env1)) in
                     let mangled_projector =
                       let uu____315 =
                         FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___149_319  ->
                                 match uu___149_319 with
                                 | FStar_Syntax_Syntax.Projector uu____320 ->
                                     true
                                 | uu____323 -> false)) in
                       if uu____315
                       then
                         let mname = mangle_projector_lid lid in
                         FStar_Pervasives_Native.Some
                           ((mname.FStar_Ident.ident).FStar_Ident.idText)
                       else FStar_Pervasives_Native.None in
                     let attrs1 = extract_attrs attrs in
                     let td =
                       let uu____343 =
                         let uu____356 = lident_as_mlsymbol lid in
                         (assumed, uu____356, mangled_projector, ml_bs,
                           attrs1,
                           (FStar_Pervasives_Native.Some
                              (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1))) in
                       [uu____343] in
                     let def3 =
                       let uu____389 =
                         let uu____390 =
                           FStar_Extraction_ML_Util.mlloc_of_range
                             (FStar_Ident.range_of_lid lid) in
                         FStar_Extraction_ML_Syntax.MLM_Loc uu____390 in
                       [uu____389; FStar_Extraction_ML_Syntax.MLM_Ty td] in
                     let env2 =
                       let uu____392 =
                         FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___150_395  ->
                                 match uu___150_395 with
                                 | FStar_Syntax_Syntax.Assumption  -> true
                                 | FStar_Syntax_Syntax.New  -> true
                                 | uu____396 -> false)) in
                       if uu____392
                       then env1
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
    let uu____525 = FStar_Syntax_Print.lid_to_string i.iname in
    let uu____526 = FStar_Syntax_Print.binders_to_string " " i.iparams in
    let uu____527 = FStar_Syntax_Print.term_to_string i.ityp in
    let uu____528 =
      let uu____529 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let uu____537 = FStar_Syntax_Print.lid_to_string d.dname in
                let uu____538 =
                  let uu____539 = FStar_Syntax_Print.term_to_string d.dtyp in
                  Prims.strcat " : " uu____539 in
                Prims.strcat uu____537 uu____538)) in
      FStar_All.pipe_right uu____529 (FStar_String.concat "\n\t\t") in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____525 uu____526 uu____527
      uu____528
let bundle_as_inductive_families env ses quals attrs =
  FStar_All.pipe_right ses
    (FStar_List.collect
       (fun se  ->
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_inductive_typ (l,_us,bs,t,_mut_i,datas)
              ->
              let uu____602 = FStar_Syntax_Subst.open_term bs t in
              (match uu____602 with
               | (bs1,t1) ->
                   let datas1 =
                     FStar_All.pipe_right ses
                       (FStar_List.collect
                          (fun se1  ->
                             match se1.FStar_Syntax_Syntax.sigel with
                             | FStar_Syntax_Syntax.Sig_datacon
                                 (d,uu____630,t2,l',nparams,uu____634) when
                                 FStar_Ident.lid_equals l l' ->
                                 let uu____637 =
                                   FStar_Syntax_Util.arrow_formals t2 in
                                 (match uu____637 with
                                  | (bs',body) ->
                                      let uu____658 =
                                        FStar_Util.first_N
                                          (FStar_List.length bs1) bs' in
                                      (match uu____658 with
                                       | (bs_params,rest) ->
                                           let subst1 =
                                             FStar_List.map2
                                               (fun uu____703  ->
                                                  fun uu____704  ->
                                                    match (uu____703,
                                                            uu____704)
                                                    with
                                                    | ((b',uu____714),
                                                       (b,uu____716)) ->
                                                        let uu____721 =
                                                          let uu____726 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              b in
                                                          (b', uu____726) in
                                                        FStar_Syntax_Syntax.NT
                                                          uu____721)
                                               bs_params bs1 in
                                           let t3 =
                                             let uu____728 =
                                               let uu____731 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   body in
                                               FStar_Syntax_Util.arrow rest
                                                 uu____731 in
                                             FStar_All.pipe_right uu____728
                                               (FStar_Syntax_Subst.subst
                                                  subst1) in
                                           [{ dname = d; dtyp = t3 }]))
                             | uu____736 -> [])) in
                   let attrs1 =
                     extract_attrs
                       (FStar_List.append se.FStar_Syntax_Syntax.sigattrs
                          attrs) in
                   [{
                      iname = l;
                      iparams = bs1;
                      ityp = t1;
                      idatas = datas1;
                      iquals = (se.FStar_Syntax_Syntax.sigquals);
                      iattrs = attrs1
                    }])
          | uu____739 -> []))
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
          let uu____782 =
            FStar_Extraction_ML_Term.term_as_mlty env1 ctor.dtyp in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env1) uu____782 in
        let steps =
          [FStar_TypeChecker_Normalize.Inlining;
          FStar_TypeChecker_Normalize.UnfoldUntil
            FStar_Syntax_Syntax.Delta_constant;
          FStar_TypeChecker_Normalize.EraseUniverses;
          FStar_TypeChecker_Normalize.AllowUnboundUniverses] in
        let names1 =
          let uu____787 =
            let uu____788 =
              let uu____791 =
                FStar_TypeChecker_Normalize.normalize steps
                  env1.FStar_Extraction_ML_UEnv.tcenv ctor.dtyp in
              FStar_Syntax_Subst.compress uu____791 in
            uu____788.FStar_Syntax_Syntax.n in
          match uu____787 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,uu____794) ->
              FStar_List.map
                (fun uu____812  ->
                   match uu____812 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____816;
                        FStar_Syntax_Syntax.sort = uu____817;_},uu____818)
                       -> ppname.FStar_Ident.idText) bs
          | uu____821 -> [] in
        let tys = (ml_tyvars, mlt) in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp in
        let uu____832 =
          let uu____833 =
            FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false in
          FStar_Pervasives_Native.fst uu____833 in
        let uu____836 =
          let uu____842 = lident_as_mlsymbol ctor.dname in
          let uu____843 =
            let uu____847 = FStar_Extraction_ML_Util.argTypes mlt in
            FStar_List.zip names1 uu____847 in
          (uu____842, uu____843) in
        (uu____832, uu____836) in
      let extract_one_family env1 ind =
        let uu____877 = binders_as_mlty_binders env1 ind.iparams in
        match uu____877 with
        | (env2,vars) ->
            let uu____904 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor vars) env2) in
            (match uu____904 with
             | (env3,ctors) ->
                 let uu____954 = FStar_Syntax_Util.arrow_formals ind.ityp in
                 (match uu____954 with
                  | (indices,uu____976) ->
                      let ml_params =
                        let uu____991 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____1009  ->
                                    let uu____1012 =
                                      let uu____1013 =
                                        FStar_Util.string_of_int i in
                                      Prims.strcat "'dummyV" uu____1013 in
                                    (uu____1012, (Prims.parse_int "0")))) in
                        FStar_List.append vars uu____991 in
                      let tbody =
                        let uu____1017 =
                          FStar_Util.find_opt
                            (fun uu___151_1021  ->
                               match uu___151_1021 with
                               | FStar_Syntax_Syntax.RecordType uu____1022 ->
                                   true
                               | uu____1027 -> false) ind.iquals in
                        match uu____1017 with
                        | FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____1034 = FStar_List.hd ctors in
                            (match uu____1034 with
                             | (uu____1045,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id  ->
                                        fun uu____1070  ->
                                          match uu____1070 with
                                          | (uu____1075,ty) ->
                                              let lid =
                                                FStar_Ident.lid_of_ids
                                                  (FStar_List.append ns [id]) in
                                              let uu____1078 =
                                                lident_as_mlsymbol lid in
                                              (uu____1078, ty)) ids c_ty in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____1079 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors in
                      let uu____1081 =
                        let uu____1093 = lident_as_mlsymbol ind.iname in
                        (false, uu____1093, FStar_Pervasives_Native.None,
                          ml_params, (ind.iattrs),
                          (FStar_Pervasives_Native.Some tbody)) in
                      (env3, uu____1081))) in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____1115,t,uu____1117,uu____1118,uu____1119);
            FStar_Syntax_Syntax.sigrng = uu____1120;
            FStar_Syntax_Syntax.sigquals = uu____1121;
            FStar_Syntax_Syntax.sigmeta = uu____1122;
            FStar_Syntax_Syntax.sigattrs = uu____1123;_}::[],uu____1124),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____1133 = extract_ctor [] env { dname = l; dtyp = t } in
          (match uu____1133 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____1160),quals) ->
          let ifams =
            bundle_as_inductive_families env ses quals
              se.FStar_Syntax_Syntax.sigattrs in
          let uu____1171 = FStar_Util.fold_map extract_one_family env ifams in
          (match uu____1171 with
           | (env1,td) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Ty td]))
      | uu____1227 -> failwith "Unexpected signature element"
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
           let uu____1252 = FStar_Syntax_Print.sigelt_to_string se in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____1252);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____1256 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____1261 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____1270 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
           ->
           let extend_env g1 lid ml_name tm tysc =
             let uu____1298 =
               let uu____1301 =
                 FStar_Syntax_Syntax.lid_as_fv lid
                   FStar_Syntax_Syntax.Delta_equational
                   FStar_Pervasives_Native.None in
               FStar_Extraction_ML_UEnv.extend_fv' g1 uu____1301 ml_name tysc
                 false false in
             match uu____1298 with
             | (g2,mangled_name) ->
                 ((let uu____1307 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          g2.FStar_Extraction_ML_UEnv.tcenv)
                       (FStar_Options.Other "ExtractionReify") in
                   if uu____1307
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
             (let uu____1319 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify") in
              if uu____1319
              then
                let uu____1320 = FStar_Syntax_Print.term_to_string tm in
                FStar_Util.print1 "extract_fv term: %s\n" uu____1320
              else ());
             (let uu____1322 =
                let uu____1323 = FStar_Syntax_Subst.compress tm in
                uu____1323.FStar_Syntax_Syntax.n in
              match uu____1322 with
              | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____1329) ->
                  extract_fv tm1
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let mlp =
                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  let uu____1336 =
                    let uu____1341 = FStar_Extraction_ML_UEnv.lookup_fv g fv in
                    FStar_All.pipe_left FStar_Util.right uu____1341 in
                  (match uu____1336 with
                   | (uu____1370,uu____1371,tysc,uu____1373) ->
                       let uu____1374 =
                         FStar_All.pipe_left
                           (FStar_Extraction_ML_Syntax.with_ty
                              FStar_Extraction_ML_Syntax.MLTY_Top)
                           (FStar_Extraction_ML_Syntax.MLE_Name mlp) in
                       (uu____1374, tysc))
              | uu____1375 -> failwith "Not an fv") in
           let extract_action g1 a =
             (let uu____1397 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g1.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify") in
              if uu____1397
              then
                let uu____1398 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_typ in
                let uu____1399 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_defn in
                FStar_Util.print2 "Action type %s and term %s\n" uu____1398
                  uu____1399
              else ());
             (let uu____1401 = FStar_Extraction_ML_UEnv.action_name ed a in
              match uu____1401 with
              | (a_nm,a_lid) ->
                  let lbname =
                    let uu____1411 =
                      FStar_Syntax_Syntax.new_bv
                        (FStar_Pervasives_Native.Some
                           ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                        FStar_Syntax_Syntax.tun in
                    FStar_Util.Inl uu____1411 in
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
                  let uu____1432 =
                    FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb in
                  (match uu____1432 with
                   | (a_let,uu____1439,ty) ->
                       ((let uu____1442 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug
                                g1.FStar_Extraction_ML_UEnv.tcenv)
                             (FStar_Options.Other "ExtractionReify") in
                         if uu____1442
                         then
                           let uu____1443 =
                             FStar_Extraction_ML_Code.string_of_mlexpr a_nm
                               a_let in
                           FStar_Util.print1 "Extracted action term: %s\n"
                             uu____1443
                         else ());
                        (let uu____1445 =
                           match a_let.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_Let
                               ((uu____1450,uu____1451,mllb::[]),uu____1453)
                               ->
                               (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                                with
                                | FStar_Pervasives_Native.Some tysc ->
                                    ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                      tysc)
                                | FStar_Pervasives_Native.None  ->
                                    failwith "No type scheme")
                           | uu____1464 -> failwith "Impossible" in
                         match uu____1445 with
                         | (exp,tysc) ->
                             ((let uu____1472 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug
                                      g1.FStar_Extraction_ML_UEnv.tcenv)
                                   (FStar_Options.Other "ExtractionReify") in
                               if uu____1472
                               then
                                 ((let uu____1474 =
                                     FStar_Extraction_ML_Code.string_of_mlty
                                       a_nm
                                       (FStar_Pervasives_Native.snd tysc) in
                                   FStar_Util.print1
                                     "Extracted action type: %s\n" uu____1474);
                                  FStar_List.iter
                                    (fun x  ->
                                       FStar_Util.print1 "and binders: %s\n"
                                         (FStar_Pervasives_Native.fst x))
                                    (FStar_Pervasives_Native.fst tysc))
                               else ());
                              extend_env g1 a_lid a_nm exp tysc))))) in
           let uu____1482 =
             let uu____1485 =
               extract_fv
                 (FStar_Pervasives_Native.snd
                    ed.FStar_Syntax_Syntax.return_repr) in
             match uu____1485 with
             | (return_tm,ty_sc) ->
                 let uu____1493 =
                   FStar_Extraction_ML_UEnv.monad_op_name ed "return" in
                 (match uu____1493 with
                  | (return_nm,return_lid) ->
                      extend_env g return_lid return_nm return_tm ty_sc) in
           (match uu____1482 with
            | (g1,return_decl) ->
                let uu____1505 =
                  let uu____1508 =
                    extract_fv
                      (FStar_Pervasives_Native.snd
                         ed.FStar_Syntax_Syntax.bind_repr) in
                  match uu____1508 with
                  | (bind_tm,ty_sc) ->
                      let uu____1516 =
                        FStar_Extraction_ML_UEnv.monad_op_name ed "bind" in
                      (match uu____1516 with
                       | (bind_nm,bind_lid) ->
                           extend_env g1 bind_lid bind_nm bind_tm ty_sc) in
                (match uu____1505 with
                 | (g2,bind_decl) ->
                     let uu____1528 =
                       FStar_Util.fold_map extract_action g2
                         ed.FStar_Syntax_Syntax.actions in
                     (match uu____1528 with
                      | (g3,actions) ->
                          (g3,
                            (FStar_List.append [return_decl; bind_decl]
                               actions)))))
       | FStar_Syntax_Syntax.Sig_new_effect uu____1540 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____1543,t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let attrs = se.FStar_Syntax_Syntax.sigattrs in
           let uu____1549 =
             let uu____1550 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___152_1553  ->
                       match uu___152_1553 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____1554 -> false)) in
             Prims.op_Negation uu____1550 in
           if uu____1549
           then (g, [])
           else
             (let uu____1560 = FStar_Syntax_Util.arrow_formals t in
              match uu____1560 with
              | (bs,uu____1572) ->
                  let fv =
                    FStar_Syntax_Syntax.lid_as_fv lid
                      FStar_Syntax_Syntax.Delta_constant
                      FStar_Pervasives_Native.None in
                  let uu____1584 =
                    FStar_Syntax_Util.abs bs FStar_TypeChecker_Common.t_unit
                      FStar_Pervasives_Native.None in
                  extract_typ_abbrev g fv quals attrs uu____1584)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____1586) when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____1595 =
             let uu____1600 =
               FStar_TypeChecker_Env.open_universes_in
                 g.FStar_Extraction_ML_UEnv.tcenv
                 lb.FStar_Syntax_Syntax.lbunivs
                 [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp] in
             match uu____1600 with
             | (tcenv,uu____1616,def_typ) ->
                 let uu____1620 = as_pair def_typ in (tcenv, uu____1620) in
           (match uu____1595 with
            | (tcenv,(lbdef,lbtyp)) ->
                let lbtyp1 =
                  FStar_TypeChecker_Normalize.unfold_whnf tcenv lbtyp in
                let lbdef1 =
                  FStar_TypeChecker_Normalize.eta_expand_with_type tcenv
                    lbdef lbtyp1 in
                let uu____1635 =
                  FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                extract_typ_abbrev g uu____1635 quals
                  se.FStar_Syntax_Syntax.sigattrs lbdef1)
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____1637) ->
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
               | FStar_Syntax_Syntax.Tm_uinst (h',uu____1663) ->
                   let uu____1668 =
                     let uu____1669 = FStar_Syntax_Subst.compress h' in
                     uu____1669.FStar_Syntax_Syntax.n in
                   (match uu____1668 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.tactic_lid
                        ->
                        let uu____1673 =
                          let uu____1674 =
                            FStar_Extraction_ML_Syntax.string_of_mlpath
                              g.FStar_Extraction_ML_UEnv.currentModule in
                          FStar_Util.starts_with uu____1674 "FStar.Tactics" in
                        Prims.op_Negation uu____1673
                    | uu____1675 -> false)
               | uu____1676 -> false in
             let mk_registration tac_lid assm_lid t bs =
               let h =
                 let uu____1697 =
                   let uu____1698 =
                     let uu____1699 =
                       FStar_Ident.lid_of_str
                         "FStar_Tactics_Native.register_tactic" in
                     FStar_Extraction_ML_Syntax.mlpath_of_lident uu____1699 in
                   FStar_Extraction_ML_Syntax.MLE_Name uu____1698 in
                 FStar_All.pipe_left
                   (FStar_Extraction_ML_Syntax.with_ty
                      FStar_Extraction_ML_Syntax.MLTY_Top) uu____1697 in
               let lid_arg =
                 let uu____1701 =
                   let uu____1702 = FStar_Ident.string_of_lid assm_lid in
                   FStar_Extraction_ML_Syntax.MLC_String uu____1702 in
                 FStar_Extraction_ML_Syntax.MLE_Const uu____1701 in
               let tac_arity = FStar_List.length bs in
               let arity =
                 let uu____1709 =
                   let uu____1710 =
                     let uu____1711 =
                       FStar_Util.string_of_int
                         (tac_arity + (Prims.parse_int "1")) in
                     FStar_Ident.lid_of_str uu____1711 in
                   FStar_Extraction_ML_Syntax.mlpath_of_lident uu____1710 in
                 FStar_Extraction_ML_Syntax.MLE_Name uu____1709 in
               let tac_interpretation =
                 FStar_Extraction_ML_Util.mk_interpretation_fun tac_lid
                   lid_arg t bs in
               let app =
                 let uu____1720 =
                   let uu____1721 =
                     let uu____1725 =
                       FStar_List.map
                         (FStar_Extraction_ML_Syntax.with_ty
                            FStar_Extraction_ML_Syntax.MLTY_Top)
                         [lid_arg; arity; tac_interpretation] in
                     (h, uu____1725) in
                   FStar_Extraction_ML_Syntax.MLE_App uu____1721 in
                 FStar_All.pipe_left
                   (FStar_Extraction_ML_Syntax.with_ty
                      FStar_Extraction_ML_Syntax.MLTY_Top) uu____1720 in
               FStar_Extraction_ML_Syntax.MLM_Top app in
             match FStar_Pervasives_Native.snd lbs with
             | hd1::[] ->
                 let uu____1731 =
                   FStar_Syntax_Util.arrow_formals_comp
                     hd1.FStar_Syntax_Syntax.lbtyp in
                 (match uu____1731 with
                  | (bs,comp) ->
                      let t = FStar_Syntax_Util.comp_result comp in
                      let uu____1749 =
                        let uu____1750 = FStar_Syntax_Subst.compress t in
                        uu____1750.FStar_Syntax_Syntax.n in
                      (match uu____1749 with
                       | FStar_Syntax_Syntax.Tm_app (h,args) ->
                           let h1 = FStar_Syntax_Subst.compress h in
                           let tac_lid =
                             let uu____1772 =
                               let uu____1774 =
                                 FStar_Util.right
                                   hd1.FStar_Syntax_Syntax.lbname in
                               uu____1774.FStar_Syntax_Syntax.fv_name in
                             uu____1772.FStar_Syntax_Syntax.v in
                           let assm_lid =
                             let uu____1776 =
                               FStar_All.pipe_left FStar_Ident.id_of_text
                                 (Prims.strcat "__"
                                    (tac_lid.FStar_Ident.ident).FStar_Ident.idText) in
                             FStar_Ident.lid_of_ns_and_id
                               tac_lid.FStar_Ident.ns uu____1776 in
                           let uu____1777 = is_tactic_decl assm_lid h1 in
                           if uu____1777
                           then
                             let uu____1779 =
                               let uu____1780 =
                                 let uu____1781 = FStar_List.hd args in
                                 FStar_Pervasives_Native.fst uu____1781 in
                               mk_registration tac_lid assm_lid uu____1780 bs in
                             [uu____1779]
                           else []
                       | uu____1793 -> []))
             | uu____1794 -> [] in
           let uu____1796 = FStar_Extraction_ML_Term.term_as_mlexpr g elet in
           (match uu____1796 with
            | (ml_let,uu____1804,uu____1805) ->
                (match ml_let.FStar_Extraction_ML_Syntax.expr with
                 | FStar_Extraction_ML_Syntax.MLE_Let
                     ((flavor,uu____1810,bindings),uu____1812) ->
                     let uu____1819 =
                       FStar_List.fold_left2
                         (fun uu____1840  ->
                            fun ml_lb  ->
                              fun uu____1842  ->
                                match (uu____1840, uu____1842) with
                                | ((env,ml_lbs),{
                                                  FStar_Syntax_Syntax.lbname
                                                    = lbname;
                                                  FStar_Syntax_Syntax.lbunivs
                                                    = uu____1855;
                                                  FStar_Syntax_Syntax.lbtyp =
                                                    t;
                                                  FStar_Syntax_Syntax.lbeff =
                                                    uu____1857;
                                                  FStar_Syntax_Syntax.lbdef =
                                                    uu____1858;_})
                                    ->
                                    let lb_lid =
                                      let uu____1872 =
                                        let uu____1874 =
                                          FStar_Util.right lbname in
                                        uu____1874.FStar_Syntax_Syntax.fv_name in
                                      uu____1872.FStar_Syntax_Syntax.v in
                                    let uu____1875 =
                                      let uu____1878 =
                                        FStar_All.pipe_right quals
                                          (FStar_Util.for_some
                                             (fun uu___153_1882  ->
                                                match uu___153_1882 with
                                                | FStar_Syntax_Syntax.Projector
                                                    uu____1883 -> true
                                                | uu____1886 -> false)) in
                                      if uu____1878
                                      then
                                        let mname =
                                          let uu____1890 =
                                            mangle_projector_lid lb_lid in
                                          FStar_All.pipe_right uu____1890
                                            FStar_Extraction_ML_Syntax.mlpath_of_lident in
                                        let uu____1891 =
                                          let uu____1894 =
                                            FStar_Util.right lbname in
                                          let uu____1895 =
                                            FStar_Util.must
                                              ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc in
                                          FStar_Extraction_ML_UEnv.extend_fv'
                                            env uu____1894 mname uu____1895
                                            ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                            false in
                                        match uu____1891 with
                                        | (env1,uu____1899) ->
                                            (env1,
                                              (let uu___158_1901 = ml_lb in
                                               {
                                                 FStar_Extraction_ML_Syntax.mllb_name
                                                   =
                                                   ((FStar_Pervasives_Native.snd
                                                       mname),
                                                     (Prims.parse_int "0"));
                                                 FStar_Extraction_ML_Syntax.mllb_tysc
                                                   =
                                                   (uu___158_1901.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                 FStar_Extraction_ML_Syntax.mllb_add_unit
                                                   =
                                                   (uu___158_1901.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                 FStar_Extraction_ML_Syntax.mllb_def
                                                   =
                                                   (uu___158_1901.FStar_Extraction_ML_Syntax.mllb_def);
                                                 FStar_Extraction_ML_Syntax.print_typ
                                                   =
                                                   (uu___158_1901.FStar_Extraction_ML_Syntax.print_typ)
                                               }))
                                      else
                                        (let uu____1904 =
                                           let uu____1905 =
                                             let uu____1908 =
                                               FStar_Util.must
                                                 ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc in
                                             FStar_Extraction_ML_UEnv.extend_lb
                                               env lbname t uu____1908
                                               ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                               false in
                                           FStar_All.pipe_left
                                             FStar_Pervasives_Native.fst
                                             uu____1905 in
                                         (uu____1904, ml_lb)) in
                                    (match uu____1875 with
                                     | (g1,ml_lb1) ->
                                         (g1, (ml_lb1 :: ml_lbs)))) (g, [])
                         bindings (FStar_Pervasives_Native.snd lbs) in
                     (match uu____1819 with
                      | (g1,ml_lbs') ->
                          let flags =
                            FStar_List.choose
                              (fun uu___154_1929  ->
                                 match uu___154_1929 with
                                 | FStar_Syntax_Syntax.Assumption  ->
                                     FStar_Pervasives_Native.Some
                                       FStar_Extraction_ML_Syntax.Assumed
                                 | FStar_Syntax_Syntax.Private  ->
                                     FStar_Pervasives_Native.Some
                                       FStar_Extraction_ML_Syntax.Private
                                 | FStar_Syntax_Syntax.NoExtract  ->
                                     FStar_Pervasives_Native.Some
                                       FStar_Extraction_ML_Syntax.NoExtract
                                 | uu____1931 -> FStar_Pervasives_Native.None)
                              quals in
                          let flags' =
                            FStar_List.choose
                              (fun uu___155_1941  ->
                                 match uu___155_1941 with
                                 | {
                                     FStar_Syntax_Syntax.n =
                                       FStar_Syntax_Syntax.Tm_constant
                                       (FStar_Const.Const_string
                                       (data,uu____1946));
                                     FStar_Syntax_Syntax.tk = uu____1947;
                                     FStar_Syntax_Syntax.pos = uu____1948;_}
                                     ->
                                     FStar_Pervasives_Native.Some
                                       (FStar_Extraction_ML_Syntax.Attribute
                                          (FStar_Util.string_of_unicode data))
                                 | uu____1952 ->
                                     (FStar_Util.print_warning
                                        "Warning: unrecognized, non-string attribute, bother protz for a better error message";
                                      FStar_Pervasives_Native.None)) attrs in
                          let uu____1956 =
                            let uu____1958 =
                              let uu____1960 =
                                let uu____1961 =
                                  FStar_Extraction_ML_Util.mlloc_of_range
                                    se.FStar_Syntax_Syntax.sigrng in
                                FStar_Extraction_ML_Syntax.MLM_Loc uu____1961 in
                              [uu____1960;
                              FStar_Extraction_ML_Syntax.MLM_Let
                                (flavor, (FStar_List.append flags flags'),
                                  (FStar_List.rev ml_lbs'))] in
                            FStar_List.append uu____1958
                              tactic_registration_decl in
                          (g1, uu____1956))
                 | uu____1965 ->
                     let uu____1966 =
                       let uu____1967 =
                         FStar_Extraction_ML_Code.string_of_mlexpr
                           g.FStar_Extraction_ML_UEnv.currentModule ml_let in
                       FStar_Util.format1
                         "Impossible: Translated a let to a non-let: %s"
                         uu____1967 in
                     failwith uu____1966))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____1972,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____1976 =
             FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption) in
           if uu____1976
           then
             let always_fail =
               let imp =
                 let uu____1983 = FStar_Syntax_Util.arrow_formals t in
                 match uu____1983 with
                 | ([],t1) ->
                     let b =
                       let uu____2002 =
                         FStar_Syntax_Syntax.gen_bv "_"
                           FStar_Pervasives_Native.None t1 in
                       FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                         uu____2002 in
                     let uu____2003 = fail_exp lid t1 in
                     FStar_Syntax_Util.abs [b] uu____2003
                       FStar_Pervasives_Native.None
                 | (bs,t1) ->
                     let uu____2016 = fail_exp lid t1 in
                     FStar_Syntax_Util.abs bs uu____2016
                       FStar_Pervasives_Native.None in
               let uu___159_2017 = se in
               let uu____2018 =
                 let uu____2019 =
                   let uu____2023 =
                     let uu____2027 =
                       let uu____2029 =
                         let uu____2030 =
                           let uu____2033 =
                             FStar_Syntax_Syntax.lid_as_fv lid
                               FStar_Syntax_Syntax.Delta_constant
                               FStar_Pervasives_Native.None in
                           FStar_Util.Inr uu____2033 in
                         {
                           FStar_Syntax_Syntax.lbname = uu____2030;
                           FStar_Syntax_Syntax.lbunivs = [];
                           FStar_Syntax_Syntax.lbtyp = t;
                           FStar_Syntax_Syntax.lbeff =
                             FStar_Parser_Const.effect_ML_lid;
                           FStar_Syntax_Syntax.lbdef = imp
                         } in
                       [uu____2029] in
                     (false, uu____2027) in
                   (uu____2023, []) in
                 FStar_Syntax_Syntax.Sig_let uu____2019 in
               {
                 FStar_Syntax_Syntax.sigel = uu____2018;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___159_2017.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___159_2017.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___159_2017.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___159_2017.FStar_Syntax_Syntax.sigattrs)
               } in
             let uu____2039 = extract_sig g always_fail in
             (match uu____2039 with
              | (g1,mlm) ->
                  let uu____2050 =
                    FStar_Util.find_map quals
                      (fun uu___156_2054  ->
                         match uu___156_2054 with
                         | FStar_Syntax_Syntax.Discriminator l ->
                             FStar_Pervasives_Native.Some l
                         | uu____2057 -> FStar_Pervasives_Native.None) in
                  (match uu____2050 with
                   | FStar_Pervasives_Native.Some l ->
                       let uu____2062 =
                         let uu____2064 =
                           let uu____2065 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____2065 in
                         let uu____2066 =
                           let uu____2068 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l in
                           [uu____2068] in
                         uu____2064 :: uu____2066 in
                       (g1, uu____2062)
                   | uu____2070 ->
                       let uu____2072 =
                         FStar_Util.find_map quals
                           (fun uu___157_2077  ->
                              match uu___157_2077 with
                              | FStar_Syntax_Syntax.Projector (l,uu____2080)
                                  -> FStar_Pervasives_Native.Some l
                              | uu____2081 -> FStar_Pervasives_Native.None) in
                       (match uu____2072 with
                        | FStar_Pervasives_Native.Some uu____2085 -> (g1, [])
                        | uu____2087 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____2093 = FStar_Extraction_ML_Term.term_as_mlexpr g e in
           (match uu____2093 with
            | (ml_main,uu____2101,uu____2102) ->
                let uu____2103 =
                  let uu____2105 =
                    let uu____2106 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____2106 in
                  [uu____2105; FStar_Extraction_ML_Syntax.MLM_Top ml_main] in
                (g, uu____2103))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____2108 ->
           failwith "impossible -- removed by tc.fs"
       | FStar_Syntax_Syntax.Sig_assume uu____2112 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____2117 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____2119 -> (g, [])
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (if p = FStar_Syntax_Syntax.LightOff
            then FStar_Options.set_ml_ish ()
            else ();
            (g, [])))
let extract_iface:
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.modul -> env_t =
  fun g  ->
    fun m  ->
      let uu____2139 =
        FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____2139 FStar_Pervasives_Native.fst
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
      (let uu____2167 = FStar_Options.debug_any () in
       if uu____2167
       then
         let uu____2168 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
         FStar_Util.print1 "Extracting module %s\n" uu____2168
       else ());
      (let uu____2170 = FStar_Options.restore_cmd_line_options true in
       let name =
         FStar_Extraction_ML_Syntax.mlpath_of_lident
           m.FStar_Syntax_Syntax.name in
       let g1 =
         let uu___160_2173 = g in
         {
           FStar_Extraction_ML_UEnv.tcenv =
             (uu___160_2173.FStar_Extraction_ML_UEnv.tcenv);
           FStar_Extraction_ML_UEnv.gamma =
             (uu___160_2173.FStar_Extraction_ML_UEnv.gamma);
           FStar_Extraction_ML_UEnv.tydefs =
             (uu___160_2173.FStar_Extraction_ML_UEnv.tydefs);
           FStar_Extraction_ML_UEnv.currentModule = name
         } in
       let uu____2174 =
         FStar_Util.fold_map extract_sig g1
           m.FStar_Syntax_Syntax.declarations in
       match uu____2174 with
       | (g2,sigs) ->
           let mlm = FStar_List.flatten sigs in
           let is_kremlin =
             let uu____2191 = FStar_Options.codegen () in
             match uu____2191 with
             | FStar_Pervasives_Native.Some "Kremlin" -> true
             | uu____2193 -> false in
           let uu____2195 =
             (((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
                (is_kremlin ||
                   (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)))
               &&
               (FStar_Options.should_extract
                  (m.FStar_Syntax_Syntax.name).FStar_Ident.str) in
           if uu____2195
           then
             ((let uu____2200 =
                 FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
               FStar_Util.print1 "Extracted module %s\n" uu____2200);
              (g2,
                [FStar_Extraction_ML_Syntax.MLLib
                   [(name, (FStar_Pervasives_Native.Some ([], mlm)),
                      (FStar_Extraction_ML_Syntax.MLLib []))]]))
           else (g2, []))