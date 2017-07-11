open Prims
let fail_exp:
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun lid  ->
    fun t  ->
      let uu____10 =
        let uu____12 =
          let uu____13 =
            let uu____21 =
              FStar_Syntax_Syntax.fvar FStar_Parser_Const.failwith_lid
                FStar_Syntax_Syntax.Delta_constant
                FStar_Pervasives_Native.None in
            let uu____22 =
              let uu____24 = FStar_Syntax_Syntax.iarg t in
              let uu____25 =
                let uu____27 =
                  let uu____28 =
                    let uu____29 =
                      let uu____31 =
                        let uu____32 =
                          let uu____33 =
                            let uu____37 =
                              let uu____38 =
                                let uu____39 =
                                  FStar_Syntax_Print.lid_to_string lid in
                                Prims.strcat "Not yet implemented:" uu____39 in
                              FStar_Bytes.string_as_unicode_bytes uu____38 in
                            (uu____37, FStar_Range.dummyRange) in
                          FStar_Const.Const_string uu____33 in
                        FStar_Syntax_Syntax.Tm_constant uu____32 in
                      FStar_Syntax_Syntax.mk uu____31 in
                    uu____29 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange in
                  FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____28 in
                [uu____27] in
              uu____24 :: uu____25 in
            (uu____21, uu____22) in
          FStar_Syntax_Syntax.Tm_app uu____13 in
        FStar_Syntax_Syntax.mk uu____12 in
      uu____10 FStar_Pervasives_Native.None FStar_Range.dummyRange
let mangle_projector_lid: FStar_Ident.lident -> FStar_Ident.lident =
  fun x  -> x
let lident_as_mlsymbol: FStar_Ident.lident -> Prims.string =
  fun id  -> (id.FStar_Ident.ident).FStar_Ident.idText
let as_pair uu___147_72 =
  match uu___147_72 with
  | a::b::[] -> (a, b)
  | uu____76 -> failwith "Expected a list with 2 elements"
let rec extract_attr:
  FStar_Syntax_Syntax.term ->
    FStar_Extraction_ML_Syntax.tyattr FStar_Pervasives_Native.option
  =
  fun x  ->
    let uu____85 = FStar_Syntax_Subst.compress x in
    match uu____85 with
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
        FStar_Syntax_Syntax.pos = uu____88;
        FStar_Syntax_Syntax.vars = uu____89;_} when
        let uu____91 =
          let uu____92 = FStar_Syntax_Syntax.lid_of_fv fv in
          FStar_Ident.string_of_lid uu____92 in
        uu____91 = "FStar.Pervasives.PpxDerivingShow" ->
        FStar_Pervasives_Native.Some
          FStar_Extraction_ML_Syntax.PpxDerivingShow
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____94;
             FStar_Syntax_Syntax.vars = uu____95;_},({
                                                       FStar_Syntax_Syntax.n
                                                         =
                                                         FStar_Syntax_Syntax.Tm_constant
                                                         (FStar_Const.Const_string
                                                         (data,uu____97));
                                                       FStar_Syntax_Syntax.pos
                                                         = uu____98;
                                                       FStar_Syntax_Syntax.vars
                                                         = uu____99;_},uu____100)::[]);
        FStar_Syntax_Syntax.pos = uu____101;
        FStar_Syntax_Syntax.vars = uu____102;_} when
        let uu____120 =
          let uu____121 = FStar_Syntax_Syntax.lid_of_fv fv in
          FStar_Ident.string_of_lid uu____121 in
        uu____120 = "FStar.Pervasives.PpxDerivingShowConstant" ->
        FStar_Pervasives_Native.Some
          (FStar_Extraction_ML_Syntax.PpxDerivingShowConstant
             (FStar_Util.string_of_unicode data))
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_meta (x1,uu____123);
        FStar_Syntax_Syntax.pos = uu____124;
        FStar_Syntax_Syntax.vars = uu____125;_} -> extract_attr x1
    | a -> FStar_Pervasives_Native.None
let extract_attrs:
  FStar_Syntax_Syntax.term Prims.list ->
    FStar_Extraction_ML_Syntax.tyattr Prims.list
  = fun attrs  -> FStar_List.choose extract_attr attrs
let binders_as_mlty_binders env bs =
  FStar_Util.fold_map
    (fun env1  ->
       fun uu____174  ->
         match uu____174 with
         | (bv,uu____182) ->
             let uu____183 =
               let uu____184 =
                 let uu____186 =
                   let uu____187 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv in
                   FStar_Extraction_ML_Syntax.MLTY_Var uu____187 in
                 FStar_Pervasives_Native.Some uu____186 in
               FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____184 in
             let uu____188 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv in
             (uu____183, uu____188)) env bs
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
              let uu____222 =
                let uu____223 = FStar_Syntax_Subst.compress def in
                FStar_All.pipe_right uu____223 FStar_Syntax_Util.unmeta in
              FStar_All.pipe_right uu____222 FStar_Syntax_Util.un_uinst in
            let def2 =
              match def1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_abs uu____225 ->
                  FStar_Extraction_ML_Term.normalize_abs def1
              | uu____234 -> def1 in
            let uu____235 =
              match def2.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____242) ->
                  FStar_Syntax_Subst.open_term bs body
              | uu____253 -> ([], def2) in
            match uu____235 with
            | (bs,body) ->
                let assumed =
                  FStar_Util.for_some
                    (fun uu___148_266  ->
                       match uu___148_266 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____267 -> false) quals in
                let uu____268 = binders_as_mlty_binders env bs in
                (match uu____268 with
                 | (env1,ml_bs) ->
                     let body1 =
                       let uu____286 =
                         FStar_Extraction_ML_Term.term_as_mlty env1 body in
                       FStar_All.pipe_right uu____286
                         (FStar_Extraction_ML_Util.eraseTypeDeep
                            (FStar_Extraction_ML_Util.udelta_unfold env1)) in
                     let mangled_projector =
                       let uu____289 =
                         FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___149_293  ->
                                 match uu___149_293 with
                                 | FStar_Syntax_Syntax.Projector uu____294 ->
                                     true
                                 | uu____297 -> false)) in
                       if uu____289
                       then
                         let mname = mangle_projector_lid lid in
                         FStar_Pervasives_Native.Some
                           ((mname.FStar_Ident.ident).FStar_Ident.idText)
                       else FStar_Pervasives_Native.None in
                     let attrs1 = extract_attrs attrs in
                     let td =
                       let uu____317 =
                         let uu____330 = lident_as_mlsymbol lid in
                         (assumed, uu____330, mangled_projector, ml_bs,
                           attrs1,
                           (FStar_Pervasives_Native.Some
                              (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1))) in
                       [uu____317] in
                     let def3 =
                       let uu____363 =
                         let uu____364 =
                           FStar_Extraction_ML_Util.mlloc_of_range
                             (FStar_Ident.range_of_lid lid) in
                         FStar_Extraction_ML_Syntax.MLM_Loc uu____364 in
                       [uu____363; FStar_Extraction_ML_Syntax.MLM_Ty td] in
                     let env2 =
                       let uu____366 =
                         FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___150_369  ->
                                 match uu___150_369 with
                                 | FStar_Syntax_Syntax.Assumption  -> true
                                 | FStar_Syntax_Syntax.New  -> true
                                 | uu____370 -> false)) in
                       if uu____366
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
    let uu____499 = FStar_Syntax_Print.lid_to_string i.iname in
    let uu____500 = FStar_Syntax_Print.binders_to_string " " i.iparams in
    let uu____501 = FStar_Syntax_Print.term_to_string i.ityp in
    let uu____502 =
      let uu____503 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let uu____511 = FStar_Syntax_Print.lid_to_string d.dname in
                let uu____512 =
                  let uu____513 = FStar_Syntax_Print.term_to_string d.dtyp in
                  Prims.strcat " : " uu____513 in
                Prims.strcat uu____511 uu____512)) in
      FStar_All.pipe_right uu____503 (FStar_String.concat "\n\t\t") in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____499 uu____500 uu____501
      uu____502
let bundle_as_inductive_families env ses quals attrs =
  FStar_All.pipe_right ses
    (FStar_List.collect
       (fun se  ->
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_inductive_typ (l,_us,bs,t,_mut_i,datas)
              ->
              let uu____576 = FStar_Syntax_Subst.open_term bs t in
              (match uu____576 with
               | (bs1,t1) ->
                   let datas1 =
                     FStar_All.pipe_right ses
                       (FStar_List.collect
                          (fun se1  ->
                             match se1.FStar_Syntax_Syntax.sigel with
                             | FStar_Syntax_Syntax.Sig_datacon
                                 (d,uu____604,t2,l',nparams,uu____608) when
                                 FStar_Ident.lid_equals l l' ->
                                 let uu____611 =
                                   FStar_Syntax_Util.arrow_formals t2 in
                                 (match uu____611 with
                                  | (bs',body) ->
                                      let uu____629 =
                                        FStar_Util.first_N
                                          (FStar_List.length bs1) bs' in
                                      (match uu____629 with
                                       | (bs_params,rest) ->
                                           let subst1 =
                                             FStar_List.map2
                                               (fun uu____674  ->
                                                  fun uu____675  ->
                                                    match (uu____674,
                                                            uu____675)
                                                    with
                                                    | ((b',uu____685),
                                                       (b,uu____687)) ->
                                                        let uu____692 =
                                                          let uu____696 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              b in
                                                          (b', uu____696) in
                                                        FStar_Syntax_Syntax.NT
                                                          uu____692)
                                               bs_params bs1 in
                                           let t3 =
                                             let uu____698 =
                                               let uu____700 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   body in
                                               FStar_Syntax_Util.arrow rest
                                                 uu____700 in
                                             FStar_All.pipe_right uu____698
                                               (FStar_Syntax_Subst.subst
                                                  subst1) in
                                           [{ dname = d; dtyp = t3 }]))
                             | uu____703 -> [])) in
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
          | uu____706 -> []))
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
          let uu____749 =
            FStar_Extraction_ML_Term.term_as_mlty env1 ctor.dtyp in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env1) uu____749 in
        let steps =
          [FStar_TypeChecker_Normalize.Inlining;
          FStar_TypeChecker_Normalize.UnfoldUntil
            FStar_Syntax_Syntax.Delta_constant;
          FStar_TypeChecker_Normalize.EraseUniverses;
          FStar_TypeChecker_Normalize.AllowUnboundUniverses] in
        let names1 =
          let uu____754 =
            let uu____755 =
              let uu____757 =
                FStar_TypeChecker_Normalize.normalize steps
                  env1.FStar_Extraction_ML_UEnv.tcenv ctor.dtyp in
              FStar_Syntax_Subst.compress uu____757 in
            uu____755.FStar_Syntax_Syntax.n in
          match uu____754 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,uu____760) ->
              FStar_List.map
                (fun uu____776  ->
                   match uu____776 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____780;
                        FStar_Syntax_Syntax.sort = uu____781;_},uu____782)
                       -> ppname.FStar_Ident.idText) bs
          | uu____784 -> [] in
        let tys = (ml_tyvars, mlt) in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp in
        let uu____795 =
          let uu____796 =
            FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false in
          FStar_Pervasives_Native.fst uu____796 in
        let uu____799 =
          let uu____805 = lident_as_mlsymbol ctor.dname in
          let uu____806 =
            let uu____810 = FStar_Extraction_ML_Util.argTypes mlt in
            FStar_List.zip names1 uu____810 in
          (uu____805, uu____806) in
        (uu____795, uu____799) in
      let extract_one_family env1 ind =
        let uu____840 = binders_as_mlty_binders env1 ind.iparams in
        match uu____840 with
        | (env2,vars) ->
            let uu____867 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor vars) env2) in
            (match uu____867 with
             | (env3,ctors) ->
                 let uu____917 = FStar_Syntax_Util.arrow_formals ind.ityp in
                 (match uu____917 with
                  | (indices,uu____938) ->
                      let ml_params =
                        let uu____951 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____969  ->
                                    let uu____972 =
                                      let uu____973 =
                                        FStar_Util.string_of_int i in
                                      Prims.strcat "'dummyV" uu____973 in
                                    (uu____972, (Prims.parse_int "0")))) in
                        FStar_List.append vars uu____951 in
                      let tbody =
                        let uu____977 =
                          FStar_Util.find_opt
                            (fun uu___151_981  ->
                               match uu___151_981 with
                               | FStar_Syntax_Syntax.RecordType uu____982 ->
                                   true
                               | uu____987 -> false) ind.iquals in
                        match uu____977 with
                        | FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____994 = FStar_List.hd ctors in
                            (match uu____994 with
                             | (uu____1005,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id  ->
                                        fun uu____1030  ->
                                          match uu____1030 with
                                          | (uu____1035,ty) ->
                                              let lid =
                                                FStar_Ident.lid_of_ids
                                                  (FStar_List.append ns [id]) in
                                              let uu____1038 =
                                                lident_as_mlsymbol lid in
                                              (uu____1038, ty)) ids c_ty in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____1039 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors in
                      let uu____1041 =
                        let uu____1053 = lident_as_mlsymbol ind.iname in
                        (false, uu____1053, FStar_Pervasives_Native.None,
                          ml_params, (ind.iattrs),
                          (FStar_Pervasives_Native.Some tbody)) in
                      (env3, uu____1041))) in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____1075,t,uu____1077,uu____1078,uu____1079);
            FStar_Syntax_Syntax.sigrng = uu____1080;
            FStar_Syntax_Syntax.sigquals = uu____1081;
            FStar_Syntax_Syntax.sigmeta = uu____1082;
            FStar_Syntax_Syntax.sigattrs = uu____1083;_}::[],uu____1084),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____1093 = extract_ctor [] env { dname = l; dtyp = t } in
          (match uu____1093 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____1120),quals) ->
          let ifams =
            bundle_as_inductive_families env ses quals
              se.FStar_Syntax_Syntax.sigattrs in
          let uu____1131 = FStar_Util.fold_map extract_one_family env ifams in
          (match uu____1131 with
           | (env1,td) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Ty td]))
      | uu____1187 -> failwith "Unexpected signature element"
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
           let uu____1212 = FStar_Syntax_Print.sigelt_to_string se in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____1212);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____1216 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____1221 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____1230 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
           ->
           let extend_env g1 lid ml_name tm tysc =
             let uu____1258 =
               let uu____1261 =
                 FStar_Syntax_Syntax.lid_as_fv lid
                   FStar_Syntax_Syntax.Delta_equational
                   FStar_Pervasives_Native.None in
               FStar_Extraction_ML_UEnv.extend_fv' g1 uu____1261 ml_name tysc
                 false false in
             match uu____1258 with
             | (g2,mangled_name) ->
                 ((let uu____1267 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          g2.FStar_Extraction_ML_UEnv.tcenv)
                       (FStar_Options.Other "ExtractionReify") in
                   if uu____1267
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
             (let uu____1279 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify") in
              if uu____1279
              then
                let uu____1280 = FStar_Syntax_Print.term_to_string tm in
                FStar_Util.print1 "extract_fv term: %s\n" uu____1280
              else ());
             (let uu____1282 =
                let uu____1283 = FStar_Syntax_Subst.compress tm in
                uu____1283.FStar_Syntax_Syntax.n in
              match uu____1282 with
              | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____1288) ->
                  extract_fv tm1
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let mlp =
                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  let uu____1293 =
                    let uu____1298 = FStar_Extraction_ML_UEnv.lookup_fv g fv in
                    FStar_All.pipe_left FStar_Util.right uu____1298 in
                  (match uu____1293 with
                   | (uu____1327,uu____1328,tysc,uu____1330) ->
                       let uu____1331 =
                         FStar_All.pipe_left
                           (FStar_Extraction_ML_Syntax.with_ty
                              FStar_Extraction_ML_Syntax.MLTY_Top)
                           (FStar_Extraction_ML_Syntax.MLE_Name mlp) in
                       (uu____1331, tysc))
              | uu____1332 -> failwith "Not an fv") in
           let extract_action g1 a =
             (let uu____1354 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g1.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify") in
              if uu____1354
              then
                let uu____1355 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_typ in
                let uu____1356 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_defn in
                FStar_Util.print2 "Action type %s and term %s\n" uu____1355
                  uu____1356
              else ());
             (let uu____1358 = FStar_Extraction_ML_UEnv.action_name ed a in
              match uu____1358 with
              | (a_nm,a_lid) ->
                  let lbname =
                    let uu____1368 =
                      FStar_Syntax_Syntax.new_bv
                        (FStar_Pervasives_Native.Some
                           ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                        FStar_Syntax_Syntax.tun in
                    FStar_Util.Inl uu____1368 in
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
                  let uu____1386 =
                    FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb in
                  (match uu____1386 with
                   | (a_let,uu____1393,ty) ->
                       ((let uu____1396 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug
                                g1.FStar_Extraction_ML_UEnv.tcenv)
                             (FStar_Options.Other "ExtractionReify") in
                         if uu____1396
                         then
                           let uu____1397 =
                             FStar_Extraction_ML_Code.string_of_mlexpr a_nm
                               a_let in
                           FStar_Util.print1 "Extracted action term: %s\n"
                             uu____1397
                         else ());
                        (let uu____1399 =
                           match a_let.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_Let
                               ((uu____1404,uu____1405,mllb::[]),uu____1407)
                               ->
                               (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                                with
                                | FStar_Pervasives_Native.Some tysc ->
                                    ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                      tysc)
                                | FStar_Pervasives_Native.None  ->
                                    failwith "No type scheme")
                           | uu____1418 -> failwith "Impossible" in
                         match uu____1399 with
                         | (exp,tysc) ->
                             ((let uu____1426 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug
                                      g1.FStar_Extraction_ML_UEnv.tcenv)
                                   (FStar_Options.Other "ExtractionReify") in
                               if uu____1426
                               then
                                 ((let uu____1428 =
                                     FStar_Extraction_ML_Code.string_of_mlty
                                       a_nm
                                       (FStar_Pervasives_Native.snd tysc) in
                                   FStar_Util.print1
                                     "Extracted action type: %s\n" uu____1428);
                                  FStar_List.iter
                                    (fun x  ->
                                       FStar_Util.print1 "and binders: %s\n"
                                         (FStar_Pervasives_Native.fst x))
                                    (FStar_Pervasives_Native.fst tysc))
                               else ());
                              extend_env g1 a_lid a_nm exp tysc))))) in
           let uu____1436 =
             let uu____1439 =
               extract_fv
                 (FStar_Pervasives_Native.snd
                    ed.FStar_Syntax_Syntax.return_repr) in
             match uu____1439 with
             | (return_tm,ty_sc) ->
                 let uu____1447 =
                   FStar_Extraction_ML_UEnv.monad_op_name ed "return" in
                 (match uu____1447 with
                  | (return_nm,return_lid) ->
                      extend_env g return_lid return_nm return_tm ty_sc) in
           (match uu____1436 with
            | (g1,return_decl) ->
                let uu____1459 =
                  let uu____1462 =
                    extract_fv
                      (FStar_Pervasives_Native.snd
                         ed.FStar_Syntax_Syntax.bind_repr) in
                  match uu____1462 with
                  | (bind_tm,ty_sc) ->
                      let uu____1470 =
                        FStar_Extraction_ML_UEnv.monad_op_name ed "bind" in
                      (match uu____1470 with
                       | (bind_nm,bind_lid) ->
                           extend_env g1 bind_lid bind_nm bind_tm ty_sc) in
                (match uu____1459 with
                 | (g2,bind_decl) ->
                     let uu____1482 =
                       FStar_Util.fold_map extract_action g2
                         ed.FStar_Syntax_Syntax.actions in
                     (match uu____1482 with
                      | (g3,actions) ->
                          (g3,
                            (FStar_List.append [return_decl; bind_decl]
                               actions)))))
       | FStar_Syntax_Syntax.Sig_new_effect uu____1494 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____1497,t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let attrs = se.FStar_Syntax_Syntax.sigattrs in
           let uu____1503 =
             let uu____1504 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___152_1507  ->
                       match uu___152_1507 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____1508 -> false)) in
             Prims.op_Negation uu____1504 in
           if uu____1503
           then (g, [])
           else
             (let uu____1514 = FStar_Syntax_Util.arrow_formals t in
              match uu____1514 with
              | (bs,uu____1525) ->
                  let fv =
                    FStar_Syntax_Syntax.lid_as_fv lid
                      FStar_Syntax_Syntax.Delta_constant
                      FStar_Pervasives_Native.None in
                  let uu____1535 =
                    FStar_Syntax_Util.abs bs FStar_TypeChecker_Common.t_unit
                      FStar_Pervasives_Native.None in
                  extract_typ_abbrev g fv quals attrs uu____1535)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____1537) when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____1546 =
             let uu____1551 =
               FStar_TypeChecker_Env.open_universes_in
                 g.FStar_Extraction_ML_UEnv.tcenv
                 lb.FStar_Syntax_Syntax.lbunivs
                 [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp] in
             match uu____1551 with
             | (tcenv,uu____1564,def_typ) ->
                 let uu____1568 = as_pair def_typ in (tcenv, uu____1568) in
           (match uu____1546 with
            | (tcenv,(lbdef,lbtyp)) ->
                let lbtyp1 =
                  FStar_TypeChecker_Normalize.unfold_whnf tcenv lbtyp in
                let lbdef1 =
                  FStar_TypeChecker_Normalize.eta_expand_with_type tcenv
                    lbdef lbtyp1 in
                let uu____1583 =
                  FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                extract_typ_abbrev g uu____1583 quals
                  se.FStar_Syntax_Syntax.sigattrs lbdef1)
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____1585) ->
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
               | FStar_Syntax_Syntax.Tm_uinst (h',uu____1608) ->
                   let uu____1611 =
                     let uu____1612 = FStar_Syntax_Subst.compress h' in
                     uu____1612.FStar_Syntax_Syntax.n in
                   (match uu____1611 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.tactic_lid
                        ->
                        let uu____1615 =
                          let uu____1616 =
                            FStar_Extraction_ML_Syntax.string_of_mlpath
                              g.FStar_Extraction_ML_UEnv.currentModule in
                          FStar_Util.starts_with uu____1616 "FStar.Tactics" in
                        Prims.op_Negation uu____1615
                    | uu____1617 -> false)
               | uu____1618 -> false in
             let mk_registration tac_lid assm_lid t bs =
               let h =
                 let uu____1639 =
                   let uu____1640 =
                     let uu____1641 =
                       FStar_Ident.lid_of_str
                         "FStar_Tactics_Native.register_tactic" in
                     FStar_Extraction_ML_Syntax.mlpath_of_lident uu____1641 in
                   FStar_Extraction_ML_Syntax.MLE_Name uu____1640 in
                 FStar_All.pipe_left
                   (FStar_Extraction_ML_Syntax.with_ty
                      FStar_Extraction_ML_Syntax.MLTY_Top) uu____1639 in
               let lid_arg =
                 let uu____1643 =
                   let uu____1644 = FStar_Ident.string_of_lid assm_lid in
                   FStar_Extraction_ML_Syntax.MLC_String uu____1644 in
                 FStar_Extraction_ML_Syntax.MLE_Const uu____1643 in
               let tac_arity = FStar_List.length bs in
               let arity =
                 let uu____1651 =
                   let uu____1652 =
                     let uu____1653 =
                       FStar_Util.string_of_int
                         (tac_arity + (Prims.parse_int "1")) in
                     FStar_Ident.lid_of_str uu____1653 in
                   FStar_Extraction_ML_Syntax.mlpath_of_lident uu____1652 in
                 FStar_Extraction_ML_Syntax.MLE_Name uu____1651 in
               let tac_interpretation =
                 FStar_Extraction_ML_Util.mk_interpretation_fun tac_lid
                   lid_arg t bs in
               let app =
                 let uu____1662 =
                   let uu____1663 =
                     let uu____1667 =
                       FStar_List.map
                         (FStar_Extraction_ML_Syntax.with_ty
                            FStar_Extraction_ML_Syntax.MLTY_Top)
                         [lid_arg; arity; tac_interpretation] in
                     (h, uu____1667) in
                   FStar_Extraction_ML_Syntax.MLE_App uu____1663 in
                 FStar_All.pipe_left
                   (FStar_Extraction_ML_Syntax.with_ty
                      FStar_Extraction_ML_Syntax.MLTY_Top) uu____1662 in
               FStar_Extraction_ML_Syntax.MLM_Top app in
             match FStar_Pervasives_Native.snd lbs with
             | hd1::[] ->
                 let uu____1673 =
                   FStar_Syntax_Util.arrow_formals_comp
                     hd1.FStar_Syntax_Syntax.lbtyp in
                 (match uu____1673 with
                  | (bs,comp) ->
                      let t = FStar_Syntax_Util.comp_result comp in
                      let uu____1690 =
                        let uu____1691 = FStar_Syntax_Subst.compress t in
                        uu____1691.FStar_Syntax_Syntax.n in
                      (match uu____1690 with
                       | FStar_Syntax_Syntax.Tm_app (h,args) ->
                           let h1 = FStar_Syntax_Subst.compress h in
                           let tac_lid =
                             let uu____1708 =
                               let uu____1710 =
                                 FStar_Util.right
                                   hd1.FStar_Syntax_Syntax.lbname in
                               uu____1710.FStar_Syntax_Syntax.fv_name in
                             uu____1708.FStar_Syntax_Syntax.v in
                           let assm_lid =
                             let uu____1712 =
                               FStar_All.pipe_left FStar_Ident.id_of_text
                                 (Prims.strcat "__"
                                    (tac_lid.FStar_Ident.ident).FStar_Ident.idText) in
                             FStar_Ident.lid_of_ns_and_id
                               tac_lid.FStar_Ident.ns uu____1712 in
                           let uu____1713 = is_tactic_decl assm_lid h1 in
                           if uu____1713
                           then
                             let uu____1715 =
                               let uu____1716 =
                                 let uu____1717 = FStar_List.hd args in
                                 FStar_Pervasives_Native.fst uu____1717 in
                               mk_registration tac_lid assm_lid uu____1716 bs in
                             [uu____1715]
                           else []
                       | uu____1726 -> []))
             | uu____1727 -> [] in
           let uu____1729 = FStar_Extraction_ML_Term.term_as_mlexpr g elet in
           (match uu____1729 with
            | (ml_let,uu____1737,uu____1738) ->
                (match ml_let.FStar_Extraction_ML_Syntax.expr with
                 | FStar_Extraction_ML_Syntax.MLE_Let
                     ((flavor,uu____1743,bindings),uu____1745) ->
                     let uu____1752 =
                       FStar_List.fold_left2
                         (fun uu____1773  ->
                            fun ml_lb  ->
                              fun uu____1775  ->
                                match (uu____1773, uu____1775) with
                                | ((env,ml_lbs),{
                                                  FStar_Syntax_Syntax.lbname
                                                    = lbname;
                                                  FStar_Syntax_Syntax.lbunivs
                                                    = uu____1788;
                                                  FStar_Syntax_Syntax.lbtyp =
                                                    t;
                                                  FStar_Syntax_Syntax.lbeff =
                                                    uu____1790;
                                                  FStar_Syntax_Syntax.lbdef =
                                                    uu____1791;_})
                                    ->
                                    let lb_lid =
                                      let uu____1803 =
                                        let uu____1805 =
                                          FStar_Util.right lbname in
                                        uu____1805.FStar_Syntax_Syntax.fv_name in
                                      uu____1803.FStar_Syntax_Syntax.v in
                                    let uu____1806 =
                                      let uu____1809 =
                                        FStar_All.pipe_right quals
                                          (FStar_Util.for_some
                                             (fun uu___153_1813  ->
                                                match uu___153_1813 with
                                                | FStar_Syntax_Syntax.Projector
                                                    uu____1814 -> true
                                                | uu____1817 -> false)) in
                                      if uu____1809
                                      then
                                        let mname =
                                          let uu____1821 =
                                            mangle_projector_lid lb_lid in
                                          FStar_All.pipe_right uu____1821
                                            FStar_Extraction_ML_Syntax.mlpath_of_lident in
                                        let uu____1822 =
                                          let uu____1825 =
                                            FStar_Util.right lbname in
                                          let uu____1826 =
                                            FStar_Util.must
                                              ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc in
                                          FStar_Extraction_ML_UEnv.extend_fv'
                                            env uu____1825 mname uu____1826
                                            ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                            false in
                                        match uu____1822 with
                                        | (env1,uu____1830) ->
                                            (env1,
                                              (let uu___158_1832 = ml_lb in
                                               {
                                                 FStar_Extraction_ML_Syntax.mllb_name
                                                   =
                                                   ((FStar_Pervasives_Native.snd
                                                       mname),
                                                     (Prims.parse_int "0"));
                                                 FStar_Extraction_ML_Syntax.mllb_tysc
                                                   =
                                                   (uu___158_1832.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                 FStar_Extraction_ML_Syntax.mllb_add_unit
                                                   =
                                                   (uu___158_1832.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                 FStar_Extraction_ML_Syntax.mllb_def
                                                   =
                                                   (uu___158_1832.FStar_Extraction_ML_Syntax.mllb_def);
                                                 FStar_Extraction_ML_Syntax.print_typ
                                                   =
                                                   (uu___158_1832.FStar_Extraction_ML_Syntax.print_typ)
                                               }))
                                      else
                                        (let uu____1835 =
                                           let uu____1836 =
                                             let uu____1839 =
                                               FStar_Util.must
                                                 ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc in
                                             FStar_Extraction_ML_UEnv.extend_lb
                                               env lbname t uu____1839
                                               ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                               false in
                                           FStar_All.pipe_left
                                             FStar_Pervasives_Native.fst
                                             uu____1836 in
                                         (uu____1835, ml_lb)) in
                                    (match uu____1806 with
                                     | (g1,ml_lb1) ->
                                         (g1, (ml_lb1 :: ml_lbs)))) (g, [])
                         bindings (FStar_Pervasives_Native.snd lbs) in
                     (match uu____1752 with
                      | (g1,ml_lbs') ->
                          let flags =
                            FStar_List.choose
                              (fun uu___154_1860  ->
                                 match uu___154_1860 with
                                 | FStar_Syntax_Syntax.Assumption  ->
                                     FStar_Pervasives_Native.Some
                                       FStar_Extraction_ML_Syntax.Assumed
                                 | FStar_Syntax_Syntax.Private  ->
                                     FStar_Pervasives_Native.Some
                                       FStar_Extraction_ML_Syntax.Private
                                 | FStar_Syntax_Syntax.NoExtract  ->
                                     FStar_Pervasives_Native.Some
                                       FStar_Extraction_ML_Syntax.NoExtract
                                 | uu____1862 -> FStar_Pervasives_Native.None)
                              quals in
                          let flags' =
                            FStar_List.choose
                              (fun uu___155_1871  ->
                                 match uu___155_1871 with
                                 | {
                                     FStar_Syntax_Syntax.n =
                                       FStar_Syntax_Syntax.Tm_constant
                                       (FStar_Const.Const_string
                                       (data,uu____1875));
                                     FStar_Syntax_Syntax.pos = uu____1876;
                                     FStar_Syntax_Syntax.vars = uu____1877;_}
                                     ->
                                     FStar_Pervasives_Native.Some
                                       (FStar_Extraction_ML_Syntax.Attribute
                                          (FStar_Util.string_of_unicode data))
                                 | uu____1881 ->
                                     (FStar_Util.print_warning
                                        "Warning: unrecognized, non-string attribute, bother protz for a better error message";
                                      FStar_Pervasives_Native.None)) attrs in
                          let uu____1884 =
                            let uu____1886 =
                              let uu____1888 =
                                let uu____1889 =
                                  FStar_Extraction_ML_Util.mlloc_of_range
                                    se.FStar_Syntax_Syntax.sigrng in
                                FStar_Extraction_ML_Syntax.MLM_Loc uu____1889 in
                              [uu____1888;
                              FStar_Extraction_ML_Syntax.MLM_Let
                                (flavor, (FStar_List.append flags flags'),
                                  (FStar_List.rev ml_lbs'))] in
                            FStar_List.append uu____1886
                              tactic_registration_decl in
                          (g1, uu____1884))
                 | uu____1893 ->
                     let uu____1894 =
                       let uu____1895 =
                         FStar_Extraction_ML_Code.string_of_mlexpr
                           g.FStar_Extraction_ML_UEnv.currentModule ml_let in
                       FStar_Util.format1
                         "Impossible: Translated a let to a non-let: %s"
                         uu____1895 in
                     failwith uu____1894))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____1900,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____1904 =
             FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption) in
           if uu____1904
           then
             let always_fail =
               let imp =
                 let uu____1911 = FStar_Syntax_Util.arrow_formals t in
                 match uu____1911 with
                 | ([],t1) ->
                     let b =
                       let uu____1927 =
                         FStar_Syntax_Syntax.gen_bv "_"
                           FStar_Pervasives_Native.None t1 in
                       FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                         uu____1927 in
                     let uu____1928 = fail_exp lid t1 in
                     FStar_Syntax_Util.abs [b] uu____1928
                       FStar_Pervasives_Native.None
                 | (bs,t1) ->
                     let uu____1939 = fail_exp lid t1 in
                     FStar_Syntax_Util.abs bs uu____1939
                       FStar_Pervasives_Native.None in
               let uu___159_1940 = se in
               let uu____1941 =
                 let uu____1942 =
                   let uu____1946 =
                     let uu____1950 =
                       let uu____1952 =
                         let uu____1953 =
                           let uu____1956 =
                             FStar_Syntax_Syntax.lid_as_fv lid
                               FStar_Syntax_Syntax.Delta_constant
                               FStar_Pervasives_Native.None in
                           FStar_Util.Inr uu____1956 in
                         {
                           FStar_Syntax_Syntax.lbname = uu____1953;
                           FStar_Syntax_Syntax.lbunivs = [];
                           FStar_Syntax_Syntax.lbtyp = t;
                           FStar_Syntax_Syntax.lbeff =
                             FStar_Parser_Const.effect_ML_lid;
                           FStar_Syntax_Syntax.lbdef = imp
                         } in
                       [uu____1952] in
                     (false, uu____1950) in
                   (uu____1946, []) in
                 FStar_Syntax_Syntax.Sig_let uu____1942 in
               {
                 FStar_Syntax_Syntax.sigel = uu____1941;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___159_1940.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___159_1940.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___159_1940.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___159_1940.FStar_Syntax_Syntax.sigattrs)
               } in
             let uu____1962 = extract_sig g always_fail in
             (match uu____1962 with
              | (g1,mlm) ->
                  let uu____1973 =
                    FStar_Util.find_map quals
                      (fun uu___156_1977  ->
                         match uu___156_1977 with
                         | FStar_Syntax_Syntax.Discriminator l ->
                             FStar_Pervasives_Native.Some l
                         | uu____1980 -> FStar_Pervasives_Native.None) in
                  (match uu____1973 with
                   | FStar_Pervasives_Native.Some l ->
                       let uu____1985 =
                         let uu____1987 =
                           let uu____1988 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____1988 in
                         let uu____1989 =
                           let uu____1991 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l in
                           [uu____1991] in
                         uu____1987 :: uu____1989 in
                       (g1, uu____1985)
                   | uu____1993 ->
                       let uu____1995 =
                         FStar_Util.find_map quals
                           (fun uu___157_2000  ->
                              match uu___157_2000 with
                              | FStar_Syntax_Syntax.Projector (l,uu____2003)
                                  -> FStar_Pervasives_Native.Some l
                              | uu____2004 -> FStar_Pervasives_Native.None) in
                       (match uu____1995 with
                        | FStar_Pervasives_Native.Some uu____2008 -> (g1, [])
                        | uu____2010 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____2016 = FStar_Extraction_ML_Term.term_as_mlexpr g e in
           (match uu____2016 with
            | (ml_main,uu____2024,uu____2025) ->
                let uu____2026 =
                  let uu____2028 =
                    let uu____2029 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____2029 in
                  [uu____2028; FStar_Extraction_ML_Syntax.MLM_Top ml_main] in
                (g, uu____2026))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____2031 ->
           failwith "impossible -- removed by tc.fs"
       | FStar_Syntax_Syntax.Sig_assume uu____2035 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____2040 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____2042 -> (g, [])
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (if p = FStar_Syntax_Syntax.LightOff
            then FStar_Options.set_ml_ish ()
            else ();
            (g, [])))
let extract_iface:
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.modul -> env_t =
  fun g  ->
    fun m  ->
      let uu____2062 =
        FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____2062 FStar_Pervasives_Native.fst
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
      (let uu____2090 = FStar_Options.debug_any () in
       if uu____2090
       then
         let uu____2091 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
         FStar_Util.print1 "Extracting module %s\n" uu____2091
       else ());
      (let uu____2093 = FStar_Options.restore_cmd_line_options true in
       let name =
         FStar_Extraction_ML_Syntax.mlpath_of_lident
           m.FStar_Syntax_Syntax.name in
       let g1 =
         let uu___160_2096 = g in
         {
           FStar_Extraction_ML_UEnv.tcenv =
             (uu___160_2096.FStar_Extraction_ML_UEnv.tcenv);
           FStar_Extraction_ML_UEnv.gamma =
             (uu___160_2096.FStar_Extraction_ML_UEnv.gamma);
           FStar_Extraction_ML_UEnv.tydefs =
             (uu___160_2096.FStar_Extraction_ML_UEnv.tydefs);
           FStar_Extraction_ML_UEnv.currentModule = name
         } in
       let uu____2097 =
         FStar_Util.fold_map extract_sig g1
           m.FStar_Syntax_Syntax.declarations in
       match uu____2097 with
       | (g2,sigs) ->
           let mlm = FStar_List.flatten sigs in
           let is_kremlin =
             let uu____2114 = FStar_Options.codegen () in
             match uu____2114 with
             | FStar_Pervasives_Native.Some "Kremlin" -> true
             | uu____2116 -> false in
           let uu____2118 =
             (((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
                (is_kremlin ||
                   (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)))
               &&
               (FStar_Options.should_extract
                  (m.FStar_Syntax_Syntax.name).FStar_Ident.str) in
           if uu____2118
           then
             ((let uu____2123 =
                 FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
               FStar_Util.print1 "Extracted module %s\n" uu____2123);
              (g2,
                [FStar_Extraction_ML_Syntax.MLLib
                   [(name, (FStar_Pervasives_Native.Some ([], mlm)),
                      (FStar_Extraction_ML_Syntax.MLLib []))]]))
           else (g2, []))