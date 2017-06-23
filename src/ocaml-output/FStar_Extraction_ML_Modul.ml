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
let binders_as_mlty_binders env bs =
  FStar_Util.fold_map
    (fun env1  ->
       fun uu____133  ->
         match uu____133 with
         | (bv,uu____141) ->
             let uu____142 =
               let uu____143 =
                 let uu____145 =
                   let uu____146 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv in
                   FStar_Extraction_ML_Syntax.MLTY_Var uu____146 in
                 FStar_Pervasives_Native.Some uu____145 in
               FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____143 in
             let uu____147 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv in
             (uu____142, uu____147)) env bs
let extract_typ_abbrev:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.term ->
          (FStar_Extraction_ML_UEnv.env,FStar_Extraction_ML_Syntax.mlmodule1
                                          Prims.list)
            FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun fv  ->
      fun quals  ->
        fun def  ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let def1 =
            let uu____175 =
              let uu____176 = FStar_Syntax_Subst.compress def in
              FStar_All.pipe_right uu____176 FStar_Syntax_Util.unmeta in
            FStar_All.pipe_right uu____175 FStar_Syntax_Util.un_uinst in
          let def2 =
            match def1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs uu____178 ->
                FStar_Extraction_ML_Term.normalize_abs def1
            | uu____188 -> def1 in
          let uu____189 =
            match def2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____196) ->
                FStar_Syntax_Subst.open_term bs body
            | uu____209 -> ([], def2) in
          match uu____189 with
          | (bs,body) ->
              let assumed =
                FStar_Util.for_some
                  (fun uu___148_222  ->
                     match uu___148_222 with
                     | FStar_Syntax_Syntax.Assumption  -> true
                     | uu____223 -> false) quals in
              let uu____224 = binders_as_mlty_binders env bs in
              (match uu____224 with
               | (env1,ml_bs) ->
                   let body1 =
                     let uu____242 =
                       FStar_Extraction_ML_Term.term_as_mlty env1 body in
                     FStar_All.pipe_right uu____242
                       (FStar_Extraction_ML_Util.eraseTypeDeep
                          (FStar_Extraction_ML_Util.udelta_unfold env1)) in
                   let mangled_projector =
                     let uu____245 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___149_249  ->
                               match uu___149_249 with
                               | FStar_Syntax_Syntax.Projector uu____250 ->
                                   true
                               | uu____253 -> false)) in
                     if uu____245
                     then
                       let mname = mangle_projector_lid lid in
                       FStar_Pervasives_Native.Some
                         ((mname.FStar_Ident.ident).FStar_Ident.idText)
                     else FStar_Pervasives_Native.None in
                   let td =
                     let uu____269 =
                       let uu____280 = lident_as_mlsymbol lid in
                       (assumed, uu____280, mangled_projector, ml_bs,
                         (FStar_Pervasives_Native.Some
                            (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1))) in
                     [uu____269] in
                   let def3 =
                     let uu____308 =
                       let uu____309 =
                         FStar_Extraction_ML_Util.mlloc_of_range
                           (FStar_Ident.range_of_lid lid) in
                       FStar_Extraction_ML_Syntax.MLM_Loc uu____309 in
                     [uu____308; FStar_Extraction_ML_Syntax.MLM_Ty td] in
                   let env2 =
                     let uu____311 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___150_314  ->
                               match uu___150_314 with
                               | FStar_Syntax_Syntax.Assumption  -> true
                               | FStar_Syntax_Syntax.New  -> true
                               | uu____315 -> false)) in
                     if uu____311
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
  iquals: FStar_Syntax_Syntax.qualifier Prims.list;}
let __proj__Mkinductive_family__item__iname:
  inductive_family -> FStar_Ident.lident =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals;_} -> __fname__iname
let __proj__Mkinductive_family__item__iparams:
  inductive_family -> FStar_Syntax_Syntax.binders =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals;_} -> __fname__iparams
let __proj__Mkinductive_family__item__ityp:
  inductive_family -> FStar_Syntax_Syntax.term =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals;_} -> __fname__ityp
let __proj__Mkinductive_family__item__idatas:
  inductive_family -> data_constructor Prims.list =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals;_} -> __fname__idatas
let __proj__Mkinductive_family__item__iquals:
  inductive_family -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals;_} -> __fname__iquals
let print_ifamily: inductive_family -> Prims.unit =
  fun i  ->
    let uu____423 = FStar_Syntax_Print.lid_to_string i.iname in
    let uu____424 = FStar_Syntax_Print.binders_to_string " " i.iparams in
    let uu____425 = FStar_Syntax_Print.term_to_string i.ityp in
    let uu____426 =
      let uu____427 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let uu____435 = FStar_Syntax_Print.lid_to_string d.dname in
                let uu____436 =
                  let uu____437 = FStar_Syntax_Print.term_to_string d.dtyp in
                  Prims.strcat " : " uu____437 in
                Prims.strcat uu____435 uu____436)) in
      FStar_All.pipe_right uu____427 (FStar_String.concat "\n\t\t") in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____423 uu____424 uu____425
      uu____426
let bundle_as_inductive_families env ses quals =
  FStar_All.pipe_right ses
    (FStar_List.collect
       (fun se  ->
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_inductive_typ (l,_us,bs,t,_mut_i,datas)
              ->
              let uu____491 = FStar_Syntax_Subst.open_term bs t in
              (match uu____491 with
               | (bs1,t1) ->
                   let datas1 =
                     FStar_All.pipe_right ses
                       (FStar_List.collect
                          (fun se1  ->
                             match se1.FStar_Syntax_Syntax.sigel with
                             | FStar_Syntax_Syntax.Sig_datacon
                                 (d,uu____519,t2,l',nparams,uu____523) when
                                 FStar_Ident.lid_equals l l' ->
                                 let uu____526 =
                                   FStar_Syntax_Util.arrow_formals t2 in
                                 (match uu____526 with
                                  | (bs',body) ->
                                      let uu____547 =
                                        FStar_Util.first_N
                                          (FStar_List.length bs1) bs' in
                                      (match uu____547 with
                                       | (bs_params,rest) ->
                                           let subst1 =
                                             FStar_List.map2
                                               (fun uu____592  ->
                                                  fun uu____593  ->
                                                    match (uu____592,
                                                            uu____593)
                                                    with
                                                    | ((b',uu____603),
                                                       (b,uu____605)) ->
                                                        let uu____610 =
                                                          let uu____615 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              b in
                                                          (b', uu____615) in
                                                        FStar_Syntax_Syntax.NT
                                                          uu____610)
                                               bs_params bs1 in
                                           let t3 =
                                             let uu____617 =
                                               let uu____620 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   body in
                                               FStar_Syntax_Util.arrow rest
                                                 uu____620 in
                                             FStar_All.pipe_right uu____617
                                               (FStar_Syntax_Subst.subst
                                                  subst1) in
                                           [{ dname = d; dtyp = t3 }]))
                             | uu____625 -> [])) in
                   [{
                      iname = l;
                      iparams = bs1;
                      ityp = t1;
                      idatas = datas1;
                      iquals = (se.FStar_Syntax_Syntax.sigquals)
                    }])
          | uu____626 -> []))
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
          let uu____669 =
            FStar_Extraction_ML_Term.term_as_mlty env1 ctor.dtyp in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env1) uu____669 in
        let steps =
          [FStar_TypeChecker_Normalize.Inlining;
          FStar_TypeChecker_Normalize.UnfoldUntil
            FStar_Syntax_Syntax.Delta_constant;
          FStar_TypeChecker_Normalize.EraseUniverses;
          FStar_TypeChecker_Normalize.AllowUnboundUniverses] in
        let names1 =
          let uu____674 =
            let uu____675 =
              let uu____678 =
                FStar_TypeChecker_Normalize.normalize steps
                  env1.FStar_Extraction_ML_UEnv.tcenv ctor.dtyp in
              FStar_Syntax_Subst.compress uu____678 in
            uu____675.FStar_Syntax_Syntax.n in
          match uu____674 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,uu____681) ->
              FStar_List.map
                (fun uu____699  ->
                   match uu____699 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____703;
                        FStar_Syntax_Syntax.sort = uu____704;_},uu____705)
                       -> ppname.FStar_Ident.idText) bs
          | uu____708 -> [] in
        let tys = (ml_tyvars, mlt) in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp in
        let uu____719 =
          let uu____720 =
            FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false in
          FStar_Pervasives_Native.fst uu____720 in
        let uu____723 =
          let uu____729 = lident_as_mlsymbol ctor.dname in
          let uu____730 =
            let uu____734 = FStar_Extraction_ML_Util.argTypes mlt in
            FStar_List.zip names1 uu____734 in
          (uu____729, uu____730) in
        (uu____719, uu____723) in
      let extract_one_family env1 ind =
        let uu____763 = binders_as_mlty_binders env1 ind.iparams in
        match uu____763 with
        | (env2,vars) ->
            let uu____789 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor vars) env2) in
            (match uu____789 with
             | (env3,ctors) ->
                 let uu____838 = FStar_Syntax_Util.arrow_formals ind.ityp in
                 (match uu____838 with
                  | (indices,uu____859) ->
                      let ml_params =
                        let uu____874 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____892  ->
                                    let uu____895 =
                                      let uu____896 =
                                        FStar_Util.string_of_int i in
                                      Prims.strcat "'dummyV" uu____896 in
                                    (uu____895, (Prims.parse_int "0")))) in
                        FStar_List.append vars uu____874 in
                      let tbody =
                        let uu____900 =
                          FStar_Util.find_opt
                            (fun uu___151_904  ->
                               match uu___151_904 with
                               | FStar_Syntax_Syntax.RecordType uu____905 ->
                                   true
                               | uu____910 -> false) ind.iquals in
                        match uu____900 with
                        | FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____917 = FStar_List.hd ctors in
                            (match uu____917 with
                             | (uu____928,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id  ->
                                        fun uu____953  ->
                                          match uu____953 with
                                          | (uu____958,ty) ->
                                              let lid =
                                                FStar_Ident.lid_of_ids
                                                  (FStar_List.append ns [id]) in
                                              let uu____961 =
                                                lident_as_mlsymbol lid in
                                              (uu____961, ty)) ids c_ty in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____962 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors in
                      let uu____964 =
                        let uu____975 = lident_as_mlsymbol ind.iname in
                        (false, uu____975, FStar_Pervasives_Native.None,
                          ml_params, (FStar_Pervasives_Native.Some tbody)) in
                      (env3, uu____964))) in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____996,t,uu____998,uu____999,uu____1000);
            FStar_Syntax_Syntax.sigrng = uu____1001;
            FStar_Syntax_Syntax.sigquals = uu____1002;
            FStar_Syntax_Syntax.sigmeta = uu____1003;_}::[],uu____1004),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____1012 = extract_ctor [] env { dname = l; dtyp = t } in
          (match uu____1012 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____1039),quals) ->
          let ifams = bundle_as_inductive_families env ses quals in
          let uu____1050 = FStar_Util.fold_map extract_one_family env ifams in
          (match uu____1050 with
           | (env1,td) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Ty td]))
      | uu____1102 -> failwith "Unexpected signature element"
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
           let uu____1127 = FStar_Syntax_Print.sigelt_to_string se in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____1127);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____1131 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____1136 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____1145 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
           ->
           let extend_env g1 lid ml_name tm tysc =
             let uu____1173 =
               let uu____1176 =
                 FStar_Syntax_Syntax.lid_as_fv lid
                   FStar_Syntax_Syntax.Delta_equational
                   FStar_Pervasives_Native.None in
               FStar_Extraction_ML_UEnv.extend_fv' g1 uu____1176 ml_name tysc
                 false false in
             match uu____1173 with
             | (g2,mangled_name) ->
                 ((let uu____1182 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          g2.FStar_Extraction_ML_UEnv.tcenv)
                       (FStar_Options.Other "ExtractionReify") in
                   if uu____1182
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
             (let uu____1194 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify") in
              if uu____1194
              then
                let uu____1195 = FStar_Syntax_Print.term_to_string tm in
                FStar_Util.print1 "extract_fv term: %s\n" uu____1195
              else ());
             (let uu____1197 =
                let uu____1198 = FStar_Syntax_Subst.compress tm in
                uu____1198.FStar_Syntax_Syntax.n in
              match uu____1197 with
              | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____1204) ->
                  extract_fv tm1
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let mlp =
                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  let uu____1211 =
                    let uu____1216 = FStar_Extraction_ML_UEnv.lookup_fv g fv in
                    FStar_All.pipe_left FStar_Util.right uu____1216 in
                  (match uu____1211 with
                   | (uu____1245,uu____1246,tysc,uu____1248) ->
                       let uu____1249 =
                         FStar_All.pipe_left
                           (FStar_Extraction_ML_Syntax.with_ty
                              FStar_Extraction_ML_Syntax.MLTY_Top)
                           (FStar_Extraction_ML_Syntax.MLE_Name mlp) in
                       (uu____1249, tysc))
              | uu____1250 -> failwith "Not an fv") in
           let extract_action g1 a =
             (let uu____1272 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g1.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify") in
              if uu____1272
              then
                let uu____1273 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_typ in
                let uu____1274 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_defn in
                FStar_Util.print2 "Action type %s and term %s\n" uu____1273
                  uu____1274
              else ());
             (let uu____1276 = FStar_Extraction_ML_UEnv.action_name ed a in
              match uu____1276 with
              | (a_nm,a_lid) ->
                  let lbname =
                    let uu____1286 =
                      FStar_Syntax_Syntax.new_bv
                        (FStar_Pervasives_Native.Some
                           ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                        FStar_Syntax_Syntax.tun in
                    FStar_Util.Inl uu____1286 in
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
                  let uu____1307 =
                    FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb in
                  (match uu____1307 with
                   | (a_let,uu____1314,ty) ->
                       ((let uu____1317 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug
                                g1.FStar_Extraction_ML_UEnv.tcenv)
                             (FStar_Options.Other "ExtractionReify") in
                         if uu____1317
                         then
                           let uu____1318 =
                             FStar_Extraction_ML_Code.string_of_mlexpr a_nm
                               a_let in
                           FStar_Util.print1 "Extracted action term: %s\n"
                             uu____1318
                         else ());
                        (let uu____1320 =
                           match a_let.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_Let
                               ((uu____1325,uu____1326,mllb::[]),uu____1328)
                               ->
                               (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                                with
                                | FStar_Pervasives_Native.Some tysc ->
                                    ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                      tysc)
                                | FStar_Pervasives_Native.None  ->
                                    failwith "No type scheme")
                           | uu____1339 -> failwith "Impossible" in
                         match uu____1320 with
                         | (exp,tysc) ->
                             ((let uu____1347 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug
                                      g1.FStar_Extraction_ML_UEnv.tcenv)
                                   (FStar_Options.Other "ExtractionReify") in
                               if uu____1347
                               then
                                 ((let uu____1349 =
                                     FStar_Extraction_ML_Code.string_of_mlty
                                       a_nm
                                       (FStar_Pervasives_Native.snd tysc) in
                                   FStar_Util.print1
                                     "Extracted action type: %s\n" uu____1349);
                                  FStar_List.iter
                                    (fun x  ->
                                       FStar_Util.print1 "and binders: %s\n"
                                         (FStar_Pervasives_Native.fst x))
                                    (FStar_Pervasives_Native.fst tysc))
                               else ());
                              extend_env g1 a_lid a_nm exp tysc))))) in
           let uu____1357 =
             let uu____1360 =
               extract_fv
                 (FStar_Pervasives_Native.snd
                    ed.FStar_Syntax_Syntax.return_repr) in
             match uu____1360 with
             | (return_tm,ty_sc) ->
                 let uu____1368 =
                   FStar_Extraction_ML_UEnv.monad_op_name ed "return" in
                 (match uu____1368 with
                  | (return_nm,return_lid) ->
                      extend_env g return_lid return_nm return_tm ty_sc) in
           (match uu____1357 with
            | (g1,return_decl) ->
                let uu____1380 =
                  let uu____1383 =
                    extract_fv
                      (FStar_Pervasives_Native.snd
                         ed.FStar_Syntax_Syntax.bind_repr) in
                  match uu____1383 with
                  | (bind_tm,ty_sc) ->
                      let uu____1391 =
                        FStar_Extraction_ML_UEnv.monad_op_name ed "bind" in
                      (match uu____1391 with
                       | (bind_nm,bind_lid) ->
                           extend_env g1 bind_lid bind_nm bind_tm ty_sc) in
                (match uu____1380 with
                 | (g2,bind_decl) ->
                     let uu____1403 =
                       FStar_Util.fold_map extract_action g2
                         ed.FStar_Syntax_Syntax.actions in
                     (match uu____1403 with
                      | (g3,actions) ->
                          (g3,
                            (FStar_List.append [return_decl; bind_decl]
                               actions)))))
       | FStar_Syntax_Syntax.Sig_new_effect uu____1415 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____1418,t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____1422 =
             let uu____1423 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___152_1426  ->
                       match uu___152_1426 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____1427 -> false)) in
             Prims.op_Negation uu____1423 in
           if uu____1422
           then (g, [])
           else
             (let uu____1433 = FStar_Syntax_Util.arrow_formals t in
              match uu____1433 with
              | (bs,uu____1445) ->
                  let fv =
                    FStar_Syntax_Syntax.lid_as_fv lid
                      FStar_Syntax_Syntax.Delta_constant
                      FStar_Pervasives_Native.None in
                  let uu____1457 =
                    FStar_Syntax_Util.abs bs FStar_TypeChecker_Common.t_unit
                      FStar_Pervasives_Native.None in
                  extract_typ_abbrev g fv quals uu____1457)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____1459,uu____1460)
           when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____1471 =
             let uu____1476 =
               FStar_TypeChecker_Env.open_universes_in
                 g.FStar_Extraction_ML_UEnv.tcenv
                 lb.FStar_Syntax_Syntax.lbunivs
                 [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp] in
             match uu____1476 with
             | (tcenv,uu____1492,def_typ) ->
                 let uu____1496 = as_pair def_typ in (tcenv, uu____1496) in
           (match uu____1471 with
            | (tcenv,(lbdef,lbtyp)) ->
                let lbtyp1 =
                  FStar_TypeChecker_Normalize.unfold_whnf tcenv lbtyp in
                let lbdef1 =
                  FStar_TypeChecker_Normalize.eta_expand_with_type tcenv
                    lbdef lbtyp1 in
                let uu____1511 =
                  FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                extract_typ_abbrev g uu____1511 quals lbdef1)
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____1513,attrs) ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let elet =
             FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_let
                  (lbs, FStar_Syntax_Util.exp_false_bool))
               FStar_Pervasives_Native.None se.FStar_Syntax_Syntax.sigrng in
           let tactic_registration_decl =
             let is_tactic_decl tac_lid h =
               match h.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_uinst (h',uu____1540) ->
                   let uu____1545 =
                     let uu____1546 = FStar_Syntax_Subst.compress h' in
                     uu____1546.FStar_Syntax_Syntax.n in
                   (match uu____1545 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.tactic_lid
                        ->
                        let uu____1550 =
                          let uu____1551 =
                            FStar_Extraction_ML_Syntax.string_of_mlpath
                              g.FStar_Extraction_ML_UEnv.currentModule in
                          FStar_Util.starts_with uu____1551 "FStar.Tactics" in
                        Prims.op_Negation uu____1550
                    | uu____1552 -> false)
               | uu____1553 -> false in
             let mk_registration tac_lid assm_lid t bs =
               let h =
                 let uu____1574 =
                   let uu____1575 =
                     let uu____1576 =
                       FStar_Ident.lid_of_str
                         "FStar_Tactics_Native.register_tactic" in
                     FStar_Extraction_ML_Syntax.mlpath_of_lident uu____1576 in
                   FStar_Extraction_ML_Syntax.MLE_Name uu____1575 in
                 FStar_All.pipe_left
                   (FStar_Extraction_ML_Syntax.with_ty
                      FStar_Extraction_ML_Syntax.MLTY_Top) uu____1574 in
               let lid_arg =
                 let uu____1578 =
                   let uu____1579 = FStar_Ident.string_of_lid assm_lid in
                   FStar_Extraction_ML_Syntax.MLC_String uu____1579 in
                 FStar_Extraction_ML_Syntax.MLE_Const uu____1578 in
               let tac_arity = FStar_List.length bs in
               let arity =
                 let uu____1586 =
                   let uu____1587 =
                     let uu____1588 =
                       FStar_Util.string_of_int
                         (tac_arity + (Prims.parse_int "1")) in
                     FStar_Ident.lid_of_str uu____1588 in
                   FStar_Extraction_ML_Syntax.mlpath_of_lident uu____1587 in
                 FStar_Extraction_ML_Syntax.MLE_Name uu____1586 in
               let tac_interpretation =
                 FStar_Extraction_ML_Util.mk_interpretation_fun tac_lid
                   lid_arg t bs in
               let app =
                 let uu____1597 =
                   let uu____1598 =
                     let uu____1602 =
                       FStar_List.map
                         (FStar_Extraction_ML_Syntax.with_ty
                            FStar_Extraction_ML_Syntax.MLTY_Top)
                         [lid_arg; arity; tac_interpretation] in
                     (h, uu____1602) in
                   FStar_Extraction_ML_Syntax.MLE_App uu____1598 in
                 FStar_All.pipe_left
                   (FStar_Extraction_ML_Syntax.with_ty
                      FStar_Extraction_ML_Syntax.MLTY_Top) uu____1597 in
               FStar_Extraction_ML_Syntax.MLM_Top app in
             match FStar_Pervasives_Native.snd lbs with
             | hd1::[] ->
                 let uu____1608 =
                   FStar_Syntax_Util.arrow_formals_comp
                     hd1.FStar_Syntax_Syntax.lbtyp in
                 (match uu____1608 with
                  | (bs,comp) ->
                      let t = FStar_Syntax_Util.comp_result comp in
                      let uu____1626 =
                        let uu____1627 = FStar_Syntax_Subst.compress t in
                        uu____1627.FStar_Syntax_Syntax.n in
                      (match uu____1626 with
                       | FStar_Syntax_Syntax.Tm_app (h,args) ->
                           let h1 = FStar_Syntax_Subst.compress h in
                           let tac_lid =
                             let uu____1649 =
                               let uu____1651 =
                                 FStar_Util.right
                                   hd1.FStar_Syntax_Syntax.lbname in
                               uu____1651.FStar_Syntax_Syntax.fv_name in
                             uu____1649.FStar_Syntax_Syntax.v in
                           let assm_lid =
                             let uu____1653 =
                               FStar_All.pipe_left FStar_Ident.id_of_text
                                 (Prims.strcat "__"
                                    (tac_lid.FStar_Ident.ident).FStar_Ident.idText) in
                             FStar_Ident.lid_of_ns_and_id
                               tac_lid.FStar_Ident.ns uu____1653 in
                           let uu____1654 = is_tactic_decl assm_lid h1 in
                           if uu____1654
                           then
                             let uu____1656 =
                               let uu____1657 =
                                 let uu____1658 = FStar_List.hd args in
                                 FStar_Pervasives_Native.fst uu____1658 in
                               mk_registration tac_lid assm_lid uu____1657 bs in
                             [uu____1656]
                           else []
                       | uu____1670 -> []))
             | uu____1671 -> [] in
           let uu____1673 = FStar_Extraction_ML_Term.term_as_mlexpr g elet in
           (match uu____1673 with
            | (ml_let,uu____1681,uu____1682) ->
                (match ml_let.FStar_Extraction_ML_Syntax.expr with
                 | FStar_Extraction_ML_Syntax.MLE_Let
                     ((flavor,uu____1687,bindings),uu____1689) ->
                     let uu____1696 =
                       FStar_List.fold_left2
                         (fun uu____1717  ->
                            fun ml_lb  ->
                              fun uu____1719  ->
                                match (uu____1717, uu____1719) with
                                | ((env,ml_lbs),{
                                                  FStar_Syntax_Syntax.lbname
                                                    = lbname;
                                                  FStar_Syntax_Syntax.lbunivs
                                                    = uu____1732;
                                                  FStar_Syntax_Syntax.lbtyp =
                                                    t;
                                                  FStar_Syntax_Syntax.lbeff =
                                                    uu____1734;
                                                  FStar_Syntax_Syntax.lbdef =
                                                    uu____1735;_})
                                    ->
                                    let lb_lid =
                                      let uu____1749 =
                                        let uu____1751 =
                                          FStar_Util.right lbname in
                                        uu____1751.FStar_Syntax_Syntax.fv_name in
                                      uu____1749.FStar_Syntax_Syntax.v in
                                    let uu____1752 =
                                      let uu____1755 =
                                        FStar_All.pipe_right quals
                                          (FStar_Util.for_some
                                             (fun uu___153_1759  ->
                                                match uu___153_1759 with
                                                | FStar_Syntax_Syntax.Projector
                                                    uu____1760 -> true
                                                | uu____1763 -> false)) in
                                      if uu____1755
                                      then
                                        let mname =
                                          let uu____1767 =
                                            mangle_projector_lid lb_lid in
                                          FStar_All.pipe_right uu____1767
                                            FStar_Extraction_ML_Syntax.mlpath_of_lident in
                                        let uu____1768 =
                                          let uu____1771 =
                                            FStar_Util.right lbname in
                                          let uu____1772 =
                                            FStar_Util.must
                                              ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc in
                                          FStar_Extraction_ML_UEnv.extend_fv'
                                            env uu____1771 mname uu____1772
                                            ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                            false in
                                        match uu____1768 with
                                        | (env1,uu____1776) ->
                                            (env1,
                                              (let uu___158_1778 = ml_lb in
                                               {
                                                 FStar_Extraction_ML_Syntax.mllb_name
                                                   =
                                                   ((FStar_Pervasives_Native.snd
                                                       mname),
                                                     (Prims.parse_int "0"));
                                                 FStar_Extraction_ML_Syntax.mllb_tysc
                                                   =
                                                   (uu___158_1778.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                 FStar_Extraction_ML_Syntax.mllb_add_unit
                                                   =
                                                   (uu___158_1778.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                 FStar_Extraction_ML_Syntax.mllb_def
                                                   =
                                                   (uu___158_1778.FStar_Extraction_ML_Syntax.mllb_def);
                                                 FStar_Extraction_ML_Syntax.print_typ
                                                   =
                                                   (uu___158_1778.FStar_Extraction_ML_Syntax.print_typ)
                                               }))
                                      else
                                        (let uu____1781 =
                                           let uu____1782 =
                                             let uu____1785 =
                                               FStar_Util.must
                                                 ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc in
                                             FStar_Extraction_ML_UEnv.extend_lb
                                               env lbname t uu____1785
                                               ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                               false in
                                           FStar_All.pipe_left
                                             FStar_Pervasives_Native.fst
                                             uu____1782 in
                                         (uu____1781, ml_lb)) in
                                    (match uu____1752 with
                                     | (g1,ml_lb1) ->
                                         (g1, (ml_lb1 :: ml_lbs)))) (g, [])
                         bindings (FStar_Pervasives_Native.snd lbs) in
                     (match uu____1696 with
                      | (g1,ml_lbs') ->
                          let flags =
                            FStar_List.choose
                              (fun uu___154_1806  ->
                                 match uu___154_1806 with
                                 | FStar_Syntax_Syntax.Assumption  ->
                                     FStar_Pervasives_Native.Some
                                       FStar_Extraction_ML_Syntax.Assumed
                                 | FStar_Syntax_Syntax.Private  ->
                                     FStar_Pervasives_Native.Some
                                       FStar_Extraction_ML_Syntax.Private
                                 | FStar_Syntax_Syntax.NoExtract  ->
                                     FStar_Pervasives_Native.Some
                                       FStar_Extraction_ML_Syntax.NoExtract
                                 | uu____1808 -> FStar_Pervasives_Native.None)
                              quals in
                          let flags' =
                            FStar_List.choose
                              (fun uu___155_1819  ->
                                 match uu___155_1819 with
                                 | {
                                     FStar_Syntax_Syntax.n =
                                       FStar_Syntax_Syntax.Tm_constant
                                       (FStar_Const.Const_string
                                       (data,uu____1824));
                                     FStar_Syntax_Syntax.tk = uu____1825;
                                     FStar_Syntax_Syntax.pos = uu____1826;
                                     FStar_Syntax_Syntax.vars = uu____1827;_}
                                     ->
                                     FStar_Pervasives_Native.Some
                                       (FStar_Extraction_ML_Syntax.Attribute
                                          (FStar_Util.string_of_unicode data))
                                 | uu____1832 ->
                                     (FStar_Util.print_warning
                                        "Warning: unrecognized, non-string attribute, bother protz for a better error message";
                                      FStar_Pervasives_Native.None)) attrs in
                          let uu____1836 =
                            let uu____1838 =
                              let uu____1840 =
                                let uu____1841 =
                                  FStar_Extraction_ML_Util.mlloc_of_range
                                    se.FStar_Syntax_Syntax.sigrng in
                                FStar_Extraction_ML_Syntax.MLM_Loc uu____1841 in
                              [uu____1840;
                              FStar_Extraction_ML_Syntax.MLM_Let
                                (flavor, (FStar_List.append flags flags'),
                                  (FStar_List.rev ml_lbs'))] in
                            FStar_List.append uu____1838
                              tactic_registration_decl in
                          (g1, uu____1836))
                 | uu____1845 ->
                     let uu____1846 =
                       let uu____1847 =
                         FStar_Extraction_ML_Code.string_of_mlexpr
                           g.FStar_Extraction_ML_UEnv.currentModule ml_let in
                       FStar_Util.format1
                         "Impossible: Translated a let to a non-let: %s"
                         uu____1847 in
                     failwith uu____1846))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____1852,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____1856 =
             FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption) in
           if uu____1856
           then
             let always_fail =
               let imp =
                 let uu____1863 = FStar_Syntax_Util.arrow_formals t in
                 match uu____1863 with
                 | ([],t1) ->
                     let b =
                       let uu____1882 =
                         FStar_Syntax_Syntax.gen_bv "_"
                           FStar_Pervasives_Native.None t1 in
                       FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                         uu____1882 in
                     let uu____1883 = fail_exp lid t1 in
                     FStar_Syntax_Util.abs [b] uu____1883
                       FStar_Pervasives_Native.None
                 | (bs,t1) ->
                     let uu____1896 = fail_exp lid t1 in
                     FStar_Syntax_Util.abs bs uu____1896
                       FStar_Pervasives_Native.None in
               let uu___159_1897 = se in
               let uu____1898 =
                 let uu____1899 =
                   let uu____1905 =
                     let uu____1909 =
                       let uu____1911 =
                         let uu____1912 =
                           let uu____1915 =
                             FStar_Syntax_Syntax.lid_as_fv lid
                               FStar_Syntax_Syntax.Delta_constant
                               FStar_Pervasives_Native.None in
                           FStar_Util.Inr uu____1915 in
                         {
                           FStar_Syntax_Syntax.lbname = uu____1912;
                           FStar_Syntax_Syntax.lbunivs = [];
                           FStar_Syntax_Syntax.lbtyp = t;
                           FStar_Syntax_Syntax.lbeff =
                             FStar_Parser_Const.effect_ML_lid;
                           FStar_Syntax_Syntax.lbdef = imp
                         } in
                       [uu____1911] in
                     (false, uu____1909) in
                   (uu____1905, [], []) in
                 FStar_Syntax_Syntax.Sig_let uu____1899 in
               {
                 FStar_Syntax_Syntax.sigel = uu____1898;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___159_1897.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___159_1897.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___159_1897.FStar_Syntax_Syntax.sigmeta)
               } in
             let uu____1922 = extract_sig g always_fail in
             (match uu____1922 with
              | (g1,mlm) ->
                  let uu____1933 =
                    FStar_Util.find_map quals
                      (fun uu___156_1937  ->
                         match uu___156_1937 with
                         | FStar_Syntax_Syntax.Discriminator l ->
                             FStar_Pervasives_Native.Some l
                         | uu____1940 -> FStar_Pervasives_Native.None) in
                  (match uu____1933 with
                   | FStar_Pervasives_Native.Some l ->
                       let uu____1945 =
                         let uu____1947 =
                           let uu____1948 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____1948 in
                         let uu____1949 =
                           let uu____1951 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l in
                           [uu____1951] in
                         uu____1947 :: uu____1949 in
                       (g1, uu____1945)
                   | uu____1953 ->
                       let uu____1955 =
                         FStar_Util.find_map quals
                           (fun uu___157_1960  ->
                              match uu___157_1960 with
                              | FStar_Syntax_Syntax.Projector (l,uu____1963)
                                  -> FStar_Pervasives_Native.Some l
                              | uu____1964 -> FStar_Pervasives_Native.None) in
                       (match uu____1955 with
                        | FStar_Pervasives_Native.Some uu____1968 -> (g1, [])
                        | uu____1970 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____1976 = FStar_Extraction_ML_Term.term_as_mlexpr g e in
           (match uu____1976 with
            | (ml_main,uu____1984,uu____1985) ->
                let uu____1986 =
                  let uu____1988 =
                    let uu____1989 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____1989 in
                  [uu____1988; FStar_Extraction_ML_Syntax.MLM_Top ml_main] in
                (g, uu____1986))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____1991 ->
           failwith "impossible -- removed by tc.fs"
       | FStar_Syntax_Syntax.Sig_assume uu____1995 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____2000 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____2002 -> (g, [])
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (if p = FStar_Syntax_Syntax.LightOff
            then FStar_Options.set_ml_ish ()
            else ();
            (g, [])))
let extract_iface:
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.modul -> env_t =
  fun g  ->
    fun m  ->
      let uu____2022 =
        FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____2022 FStar_Pervasives_Native.fst
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
      (let uu____2050 = FStar_Options.debug_any () in
       if uu____2050
       then
         let uu____2051 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
         FStar_Util.print1 "Extracting module %s\n" uu____2051
       else ());
      (let uu____2053 = FStar_Options.restore_cmd_line_options true in
       let name =
         FStar_Extraction_ML_Syntax.mlpath_of_lident
           m.FStar_Syntax_Syntax.name in
       let g1 =
         let uu___160_2056 = g in
         {
           FStar_Extraction_ML_UEnv.tcenv =
             (uu___160_2056.FStar_Extraction_ML_UEnv.tcenv);
           FStar_Extraction_ML_UEnv.gamma =
             (uu___160_2056.FStar_Extraction_ML_UEnv.gamma);
           FStar_Extraction_ML_UEnv.tydefs =
             (uu___160_2056.FStar_Extraction_ML_UEnv.tydefs);
           FStar_Extraction_ML_UEnv.currentModule = name
         } in
       let uu____2057 =
         FStar_Util.fold_map extract_sig g1
           m.FStar_Syntax_Syntax.declarations in
       match uu____2057 with
       | (g2,sigs) ->
           let mlm = FStar_List.flatten sigs in
           let is_kremlin =
             let uu____2074 = FStar_Options.codegen () in
             match uu____2074 with
             | FStar_Pervasives_Native.Some "Kremlin" -> true
             | uu____2076 -> false in
           let uu____2078 =
             (((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
                (is_kremlin ||
                   (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)))
               &&
               (FStar_Options.should_extract
                  (m.FStar_Syntax_Syntax.name).FStar_Ident.str) in
           if uu____2078
           then
             ((let uu____2083 =
                 FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
               FStar_Util.print1 "Extracted module %s\n" uu____2083);
              (g2,
                [FStar_Extraction_ML_Syntax.MLLib
                   [(name, (FStar_Pervasives_Native.Some ([], mlm)),
                      (FStar_Extraction_ML_Syntax.MLLib []))]]))
           else (g2, []))