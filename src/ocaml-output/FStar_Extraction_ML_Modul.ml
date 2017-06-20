open Prims
let fail_exp lid t =
  let uu____18 =
    let uu____21 =
      let uu____22 =
        let uu____32 =
          FStar_Syntax_Syntax.fvar FStar_Syntax_Const.failwith_lid
            FStar_Syntax_Syntax.Delta_constant None in
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
                uu____40 None FStar_Range.dummyRange in
              FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____39 in
            [uu____38] in
          uu____35 :: uu____36 in
        (uu____32, uu____33) in
      FStar_Syntax_Syntax.Tm_app uu____22 in
    FStar_Syntax_Syntax.mk uu____21 in
  uu____18 None FStar_Range.dummyRange
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
       fun uu____127  ->
         match uu____127 with
         | (bv,uu____135) ->
             let uu____136 =
               let uu____137 =
                 let uu____139 =
                   let uu____140 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv in
                   FStar_Extraction_ML_Syntax.MLTY_Var uu____140 in
                 Some uu____139 in
               FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____137 in
             let uu____141 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv in
             (uu____136, uu____141)) env bs
let extract_typ_abbrev:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.term ->
          (FStar_Extraction_ML_UEnv.env* FStar_Extraction_ML_Syntax.mlmodule1
            Prims.list)
  =
  fun env  ->
    fun fv  ->
      fun quals  ->
        fun def  ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let def1 =
            let uu____173 =
              let uu____174 = FStar_Syntax_Subst.compress def in
              FStar_All.pipe_right uu____174 FStar_Syntax_Util.unmeta in
            FStar_All.pipe_right uu____173 FStar_Syntax_Util.un_uinst in
          let def2 =
            match def1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs uu____176 ->
                FStar_Extraction_ML_Term.normalize_abs def1
            | uu____186 -> def1 in
          let uu____187 =
            match def2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____194) ->
                FStar_Syntax_Subst.open_term bs body
            | uu____207 -> ([], def2) in
          match uu____187 with
          | (bs,body) ->
              let assumed =
                FStar_Util.for_some
                  (fun uu___148_219  ->
                     match uu___148_219 with
                     | FStar_Syntax_Syntax.Assumption  -> true
                     | uu____220 -> false) quals in
              let uu____221 = binders_as_mlty_binders env bs in
              (match uu____221 with
               | (env1,ml_bs) ->
                   let body1 =
                     let uu____239 =
                       FStar_Extraction_ML_Term.term_as_mlty env1 body in
                     FStar_All.pipe_right uu____239
                       (FStar_Extraction_ML_Util.eraseTypeDeep
                          (FStar_Extraction_ML_Util.udelta_unfold env1)) in
                   let mangled_projector =
                     let uu____242 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___149_244  ->
                               match uu___149_244 with
                               | FStar_Syntax_Syntax.Projector uu____245 ->
                                   true
                               | uu____248 -> false)) in
                     if uu____242
                     then
                       let mname = mangle_projector_lid lid in
                       Some ((mname.FStar_Ident.ident).FStar_Ident.idText)
                     else None in
                   let td =
                     let uu____264 =
                       let uu____275 = lident_as_mlsymbol lid in
                       (assumed, uu____275, mangled_projector, ml_bs,
                         (Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1))) in
                     [uu____264] in
                   let def3 =
                     let uu____303 =
                       let uu____304 =
                         FStar_Extraction_ML_Util.mlloc_of_range
                           (FStar_Ident.range_of_lid lid) in
                       FStar_Extraction_ML_Syntax.MLM_Loc uu____304 in
                     [uu____303; FStar_Extraction_ML_Syntax.MLM_Ty td] in
                   let env2 =
                     let uu____306 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___150_308  ->
                               match uu___150_308 with
                               | FStar_Syntax_Syntax.Assumption  -> true
                               | FStar_Syntax_Syntax.New  -> true
                               | uu____309 -> false)) in
                     if uu____306
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
    let uu____385 = FStar_Syntax_Print.lid_to_string i.iname in
    let uu____386 = FStar_Syntax_Print.binders_to_string " " i.iparams in
    let uu____387 = FStar_Syntax_Print.term_to_string i.ityp in
    let uu____388 =
      let uu____389 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let uu____394 = FStar_Syntax_Print.lid_to_string d.dname in
                let uu____395 =
                  let uu____396 = FStar_Syntax_Print.term_to_string d.dtyp in
                  Prims.strcat " : " uu____396 in
                Prims.strcat uu____394 uu____395)) in
      FStar_All.pipe_right uu____389 (FStar_String.concat "\n\t\t") in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____385 uu____386 uu____387
      uu____388
let bundle_as_inductive_families env ses quals =
  FStar_All.pipe_right ses
    (FStar_List.collect
       (fun se  ->
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_inductive_typ (l,_us,bs,t,_mut_i,datas)
              ->
              let uu____439 = FStar_Syntax_Subst.open_term bs t in
              (match uu____439 with
               | (bs1,t1) ->
                   let datas1 =
                     FStar_All.pipe_right ses
                       (FStar_List.collect
                          (fun se1  ->
                             match se1.FStar_Syntax_Syntax.sigel with
                             | FStar_Syntax_Syntax.Sig_datacon
                                 (d,uu____452,t2,l',nparams,uu____456) when
                                 FStar_Ident.lid_equals l l' ->
                                 let uu____459 =
                                   FStar_Syntax_Util.arrow_formals t2 in
                                 (match uu____459 with
                                  | (bs',body) ->
                                      let uu____480 =
                                        FStar_Util.first_N
                                          (FStar_List.length bs1) bs' in
                                      (match uu____480 with
                                       | (bs_params,rest) ->
                                           let subst1 =
                                             FStar_List.map2
                                               (fun uu____518  ->
                                                  fun uu____519  ->
                                                    match (uu____518,
                                                            uu____519)
                                                    with
                                                    | ((b',uu____529),
                                                       (b,uu____531)) ->
                                                        let uu____536 =
                                                          let uu____541 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              b in
                                                          (b', uu____541) in
                                                        FStar_Syntax_Syntax.NT
                                                          uu____536)
                                               bs_params bs1 in
                                           let t3 =
                                             let uu____543 =
                                               let uu____546 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   body in
                                               FStar_Syntax_Util.arrow rest
                                                 uu____546 in
                                             FStar_All.pipe_right uu____543
                                               (FStar_Syntax_Subst.subst
                                                  subst1) in
                                           [{ dname = d; dtyp = t3 }]))
                             | uu____551 -> [])) in
                   [{
                      iname = l;
                      iparams = bs1;
                      ityp = t1;
                      idatas = datas1;
                      iquals = (se.FStar_Syntax_Syntax.sigquals)
                    }])
          | uu____552 -> []))
type env_t = FStar_Extraction_ML_UEnv.env
let extract_bundle:
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t* FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
  =
  fun env  ->
    fun se  ->
      let extract_ctor ml_tyvars env1 ctor =
        let mlt =
          let uu____595 =
            FStar_Extraction_ML_Term.term_as_mlty env1 ctor.dtyp in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env1) uu____595 in
        let steps =
          [FStar_TypeChecker_Normalize.Inlining;
          FStar_TypeChecker_Normalize.UnfoldUntil
            FStar_Syntax_Syntax.Delta_constant;
          FStar_TypeChecker_Normalize.EraseUniverses;
          FStar_TypeChecker_Normalize.AllowUnboundUniverses] in
        let names1 =
          let uu____600 =
            let uu____601 =
              let uu____604 =
                FStar_TypeChecker_Normalize.normalize steps
                  env1.FStar_Extraction_ML_UEnv.tcenv ctor.dtyp in
              FStar_Syntax_Subst.compress uu____604 in
            uu____601.FStar_Syntax_Syntax.n in
          match uu____600 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,uu____607) ->
              FStar_List.map
                (fun uu____620  ->
                   match uu____620 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____624;
                        FStar_Syntax_Syntax.sort = uu____625;_},uu____626)
                       -> ppname.FStar_Ident.idText) bs
          | uu____629 -> [] in
        let tys = (ml_tyvars, mlt) in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp in
        let uu____640 =
          let uu____641 =
            FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false in
          fst uu____641 in
        let uu____644 =
          let uu____650 = lident_as_mlsymbol ctor.dname in
          let uu____651 =
            let uu____655 = FStar_Extraction_ML_Util.argTypes mlt in
            FStar_List.zip names1 uu____655 in
          (uu____650, uu____651) in
        (uu____640, uu____644) in
      let extract_one_family env1 ind =
        let uu____684 = binders_as_mlty_binders env1 ind.iparams in
        match uu____684 with
        | (env2,vars) ->
            let uu____710 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor vars) env2) in
            (match uu____710 with
             | (env3,ctors) ->
                 let uu____759 = FStar_Syntax_Util.arrow_formals ind.ityp in
                 (match uu____759 with
                  | (indices,uu____780) ->
                      let ml_params =
                        let uu____795 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____810  ->
                                    let uu____813 =
                                      let uu____814 =
                                        FStar_Util.string_of_int i in
                                      Prims.strcat "'dummyV" uu____814 in
                                    (uu____813, (Prims.parse_int "0")))) in
                        FStar_List.append vars uu____795 in
                      let tbody =
                        let uu____818 =
                          FStar_Util.find_opt
                            (fun uu___151_820  ->
                               match uu___151_820 with
                               | FStar_Syntax_Syntax.RecordType uu____821 ->
                                   true
                               | uu____826 -> false) ind.iquals in
                        match uu____818 with
                        | Some (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____833 = FStar_List.hd ctors in
                            (match uu____833 with
                             | (uu____844,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id  ->
                                        fun uu____862  ->
                                          match uu____862 with
                                          | (uu____867,ty) ->
                                              let lid =
                                                FStar_Ident.lid_of_ids
                                                  (FStar_List.append ns [id]) in
                                              let uu____870 =
                                                lident_as_mlsymbol lid in
                                              (uu____870, ty)) ids c_ty in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____871 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors in
                      let uu____873 =
                        let uu____884 = lident_as_mlsymbol ind.iname in
                        (false, uu____884, None, ml_params, (Some tbody)) in
                      (env3, uu____873))) in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____905,t,uu____907,uu____908,uu____909);
            FStar_Syntax_Syntax.sigrng = uu____910;
            FStar_Syntax_Syntax.sigquals = uu____911;
            FStar_Syntax_Syntax.sigmeta = uu____912;_}::[],uu____913),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____921 = extract_ctor [] env { dname = l; dtyp = t } in
          (match uu____921 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____948),quals) ->
          let ifams = bundle_as_inductive_families env ses quals in
          let uu____959 = FStar_Util.fold_map extract_one_family env ifams in
          (match uu____959 with
           | (env1,td) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Ty td]))
      | uu____1011 -> failwith "Unexpected signature element"
let rec extract_sig:
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t* FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
  =
  fun g  ->
    fun se  ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u  ->
           let uu____1034 = FStar_Syntax_Print.sigelt_to_string se in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____1034);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____1038 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____1043 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____1052 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
           ->
           let extend_env g1 lid ml_name tm tysc =
             let uu____1080 =
               let uu____1083 =
                 FStar_Syntax_Syntax.lid_as_fv lid
                   FStar_Syntax_Syntax.Delta_equational None in
               FStar_Extraction_ML_UEnv.extend_fv' g1 uu____1083 ml_name tysc
                 false false in
             match uu____1080 with
             | (g2,mangled_name) ->
                 ((let uu____1089 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          g2.FStar_Extraction_ML_UEnv.tcenv)
                       (FStar_Options.Other "ExtractionReify") in
                   if uu____1089
                   then
                     FStar_Util.print1 "Mangled name: %s\n"
                       (fst mangled_name)
                   else ());
                  (let lb =
                     {
                       FStar_Extraction_ML_Syntax.mllb_name = mangled_name;
                       FStar_Extraction_ML_Syntax.mllb_tysc = None;
                       FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                       FStar_Extraction_ML_Syntax.mllb_def = tm;
                       FStar_Extraction_ML_Syntax.print_typ = false
                     } in
                   (g2,
                     (FStar_Extraction_ML_Syntax.MLM_Let
                        (FStar_Extraction_ML_Syntax.NonRec, [], [lb]))))) in
           let rec extract_fv tm =
             (let uu____1101 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify") in
              if uu____1101
              then
                let uu____1102 = FStar_Syntax_Print.term_to_string tm in
                FStar_Util.print1 "extract_fv term: %s\n" uu____1102
              else ());
             (let uu____1104 =
                let uu____1105 = FStar_Syntax_Subst.compress tm in
                uu____1105.FStar_Syntax_Syntax.n in
              match uu____1104 with
              | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____1111) ->
                  extract_fv tm1
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let mlp =
                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  let uu____1122 =
                    let uu____1127 = FStar_Extraction_ML_UEnv.lookup_fv g fv in
                    FStar_All.pipe_left FStar_Util.right uu____1127 in
                  (match uu____1122 with
                   | (uu____1156,uu____1157,tysc,uu____1159) ->
                       let uu____1160 =
                         FStar_All.pipe_left
                           (FStar_Extraction_ML_Syntax.with_ty
                              FStar_Extraction_ML_Syntax.MLTY_Top)
                           (FStar_Extraction_ML_Syntax.MLE_Name mlp) in
                       (uu____1160, tysc))
              | uu____1161 -> failwith "Not an fv") in
           let extract_action g1 a =
             (let uu____1177 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g1.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify") in
              if uu____1177
              then
                let uu____1178 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_typ in
                let uu____1179 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_defn in
                FStar_Util.print2 "Action type %s and term %s\n" uu____1178
                  uu____1179
              else ());
             (let uu____1181 = FStar_Extraction_ML_UEnv.action_name ed a in
              match uu____1181 with
              | (a_nm,a_lid) ->
                  let lbname =
                    let uu____1191 =
                      FStar_Syntax_Syntax.new_bv
                        (Some
                           ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                        FStar_Syntax_Syntax.tun in
                    FStar_Util.Inl uu____1191 in
                  let lb =
                    FStar_Syntax_Syntax.mk_lb
                      (lbname, (a.FStar_Syntax_Syntax.action_univs),
                        FStar_Syntax_Const.effect_Tot_lid,
                        (a.FStar_Syntax_Syntax.action_typ),
                        (a.FStar_Syntax_Syntax.action_defn)) in
                  let lbs = (false, [lb]) in
                  let action_lb =
                    (FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_let
                          (lbs, FStar_Syntax_Const.exp_false_bool))) None
                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                  let uu____1214 =
                    FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb in
                  (match uu____1214 with
                   | (a_let,uu____1221,ty) ->
                       ((let uu____1224 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug
                                g1.FStar_Extraction_ML_UEnv.tcenv)
                             (FStar_Options.Other "ExtractionReify") in
                         if uu____1224
                         then
                           let uu____1225 =
                             FStar_Extraction_ML_Code.string_of_mlexpr a_nm
                               a_let in
                           FStar_Util.print1 "Extracted action term: %s\n"
                             uu____1225
                         else ());
                        (let uu____1227 =
                           match a_let.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_Let
                               ((uu____1232,uu____1233,mllb::[]),uu____1235)
                               ->
                               (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                                with
                                | Some tysc ->
                                    ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                      tysc)
                                | None  -> failwith "No type scheme")
                           | uu____1246 -> failwith "Impossible" in
                         match uu____1227 with
                         | (exp,tysc) ->
                             ((let uu____1254 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug
                                      g1.FStar_Extraction_ML_UEnv.tcenv)
                                   (FStar_Options.Other "ExtractionReify") in
                               if uu____1254
                               then
                                 ((let uu____1256 =
                                     FStar_Extraction_ML_Code.string_of_mlty
                                       a_nm (snd tysc) in
                                   FStar_Util.print1
                                     "Extracted action type: %s\n" uu____1256);
                                  FStar_List.iter
                                    (fun x  ->
                                       FStar_Util.print1 "and binders: %s\n"
                                         (fst x)) (fst tysc))
                               else ());
                              extend_env g1 a_lid a_nm exp tysc))))) in
           let uu____1263 =
             let uu____1266 =
               extract_fv (snd ed.FStar_Syntax_Syntax.return_repr) in
             match uu____1266 with
             | (return_tm,ty_sc) ->
                 let uu____1274 =
                   FStar_Extraction_ML_UEnv.monad_op_name ed "return" in
                 (match uu____1274 with
                  | (return_nm,return_lid) ->
                      extend_env g return_lid return_nm return_tm ty_sc) in
           (match uu____1263 with
            | (g1,return_decl) ->
                let uu____1286 =
                  let uu____1289 =
                    extract_fv (snd ed.FStar_Syntax_Syntax.bind_repr) in
                  match uu____1289 with
                  | (bind_tm,ty_sc) ->
                      let uu____1297 =
                        FStar_Extraction_ML_UEnv.monad_op_name ed "bind" in
                      (match uu____1297 with
                       | (bind_nm,bind_lid) ->
                           extend_env g1 bind_lid bind_nm bind_tm ty_sc) in
                (match uu____1286 with
                 | (g2,bind_decl) ->
                     let uu____1309 =
                       FStar_Util.fold_map extract_action g2
                         ed.FStar_Syntax_Syntax.actions in
                     (match uu____1309 with
                      | (g3,actions) ->
                          (g3,
                            (FStar_List.append [return_decl; bind_decl]
                               actions)))))
       | FStar_Syntax_Syntax.Sig_new_effect uu____1321 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____1324,t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____1328 =
             let uu____1329 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___152_1331  ->
                       match uu___152_1331 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____1332 -> false)) in
             Prims.op_Negation uu____1329 in
           if uu____1328
           then (g, [])
           else
             (let uu____1338 = FStar_Syntax_Util.arrow_formals t in
              match uu____1338 with
              | (bs,uu____1350) ->
                  let fv =
                    FStar_Syntax_Syntax.lid_as_fv lid
                      FStar_Syntax_Syntax.Delta_constant None in
                  let uu____1362 =
                    FStar_Syntax_Util.abs bs FStar_TypeChecker_Common.t_unit
                      None in
                  extract_typ_abbrev g fv quals uu____1362)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____1364,uu____1365)
           when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____1376 =
             let uu____1381 =
               FStar_TypeChecker_Env.open_universes_in
                 g.FStar_Extraction_ML_UEnv.tcenv
                 lb.FStar_Syntax_Syntax.lbunivs
                 [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp] in
             match uu____1381 with
             | (tcenv,uu____1397,def_typ) ->
                 let uu____1401 = as_pair def_typ in (tcenv, uu____1401) in
           (match uu____1376 with
            | (tcenv,(lbdef,lbtyp)) ->
                let lbtyp1 =
                  FStar_TypeChecker_Normalize.unfold_whnf tcenv lbtyp in
                let lbdef1 =
                  FStar_TypeChecker_Normalize.eta_expand_with_type tcenv
                    lbdef lbtyp1 in
                let uu____1416 =
                  FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                extract_typ_abbrev g uu____1416 quals lbdef1)
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____1418,attrs) ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let elet =
             FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_let
                  (lbs, FStar_Syntax_Const.exp_false_bool)) None
               se.FStar_Syntax_Syntax.sigrng in
           let tactic_registration_decl =
             let is_tactic_decl tac_lid h =
               match h.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_uinst (h',uu____1443) ->
                   let uu____1448 =
                     let uu____1449 = FStar_Syntax_Subst.compress h' in
                     uu____1449.FStar_Syntax_Syntax.n in
                   (match uu____1448 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Syntax_Const.tactic_lid
                        ->
                        let uu____1453 =
                          let uu____1454 =
                            FStar_Extraction_ML_Syntax.string_of_mlpath
                              g.FStar_Extraction_ML_UEnv.currentModule in
                          FStar_Util.starts_with uu____1454 "FStar.Tactics" in
                        Prims.op_Negation uu____1453
                    | uu____1455 -> false)
               | uu____1456 -> false in
             let mk_registration tac_lid assm_lid t bs =
               let h =
                 let uu____1481 =
                   let uu____1482 =
                     let uu____1483 =
                       FStar_Ident.lid_of_str
                         "FStar_Tactics_Native.register_tactic" in
                     FStar_Extraction_ML_Syntax.mlpath_of_lident uu____1483 in
                   FStar_Extraction_ML_Syntax.MLE_Name uu____1482 in
                 FStar_All.pipe_left
                   (FStar_Extraction_ML_Syntax.with_ty
                      FStar_Extraction_ML_Syntax.MLTY_Top) uu____1481 in
               let lid_arg =
                 let uu____1485 =
                   let uu____1486 = FStar_Ident.string_of_lid assm_lid in
                   FStar_Extraction_ML_Syntax.MLC_String uu____1486 in
                 FStar_Extraction_ML_Syntax.MLE_Const uu____1485 in
               let tac_arity = FStar_List.length bs in
               let arity =
                 let uu____1493 =
                   let uu____1494 =
                     let uu____1495 =
                       FStar_Util.string_of_int
                         (tac_arity + (Prims.parse_int "1")) in
                     FStar_Ident.lid_of_str uu____1495 in
                   FStar_Extraction_ML_Syntax.mlpath_of_lident uu____1494 in
                 FStar_Extraction_ML_Syntax.MLE_Name uu____1493 in
               let tac_interpretation =
                 FStar_Extraction_ML_Util.mk_interpretation_fun tac_lid
                   lid_arg t bs in
               let app =
                 let uu____1504 =
                   let uu____1505 =
                     let uu____1509 =
                       FStar_List.map
                         (FStar_Extraction_ML_Syntax.with_ty
                            FStar_Extraction_ML_Syntax.MLTY_Top)
                         [lid_arg; arity; tac_interpretation] in
                     (h, uu____1509) in
                   FStar_Extraction_ML_Syntax.MLE_App uu____1505 in
                 FStar_All.pipe_left
                   (FStar_Extraction_ML_Syntax.with_ty
                      FStar_Extraction_ML_Syntax.MLTY_Top) uu____1504 in
               FStar_Extraction_ML_Syntax.MLM_Top app in
             match snd lbs with
             | hd1::[] ->
                 let uu____1515 =
                   FStar_Syntax_Util.arrow_formals_comp
                     hd1.FStar_Syntax_Syntax.lbtyp in
                 (match uu____1515 with
                  | (bs,comp) ->
                      let t = FStar_Syntax_Util.comp_result comp in
                      let uu____1533 =
                        let uu____1534 = FStar_Syntax_Subst.compress t in
                        uu____1534.FStar_Syntax_Syntax.n in
                      (match uu____1533 with
                       | FStar_Syntax_Syntax.Tm_app (h,args) ->
                           let h1 = FStar_Syntax_Subst.compress h in
                           let tac_lid =
                             let uu____1556 =
                               let uu____1561 =
                                 FStar_Util.right
                                   hd1.FStar_Syntax_Syntax.lbname in
                               uu____1561.FStar_Syntax_Syntax.fv_name in
                             uu____1556.FStar_Syntax_Syntax.v in
                           let assm_lid =
                             let uu____1566 =
                               FStar_All.pipe_left FStar_Ident.id_of_text
                                 (Prims.strcat "__"
                                    (tac_lid.FStar_Ident.ident).FStar_Ident.idText) in
                             FStar_Ident.lid_of_ns_and_id
                               tac_lid.FStar_Ident.ns uu____1566 in
                           let uu____1567 = is_tactic_decl assm_lid h1 in
                           if uu____1567
                           then
                             let uu____1569 =
                               let uu____1570 =
                                 let uu____1573 = FStar_List.hd args in
                                 fst uu____1573 in
                               mk_registration tac_lid assm_lid uu____1570 bs in
                             [uu____1569]
                           else []
                       | uu____1585 -> []))
             | uu____1586 -> [] in
           let uu____1588 = FStar_Extraction_ML_Term.term_as_mlexpr g elet in
           (match uu____1588 with
            | (ml_let,uu____1596,uu____1597) ->
                (match ml_let.FStar_Extraction_ML_Syntax.expr with
                 | FStar_Extraction_ML_Syntax.MLE_Let
                     ((flavor,uu____1602,bindings),uu____1604) ->
                     let uu____1611 =
                       FStar_List.fold_left2
                         (fun uu____1618  ->
                            fun ml_lb  ->
                              fun uu____1620  ->
                                match (uu____1618, uu____1620) with
                                | ((env,ml_lbs),{
                                                  FStar_Syntax_Syntax.lbname
                                                    = lbname;
                                                  FStar_Syntax_Syntax.lbunivs
                                                    = uu____1633;
                                                  FStar_Syntax_Syntax.lbtyp =
                                                    t;
                                                  FStar_Syntax_Syntax.lbeff =
                                                    uu____1635;
                                                  FStar_Syntax_Syntax.lbdef =
                                                    uu____1636;_})
                                    ->
                                    let lb_lid =
                                      let uu____1650 =
                                        let uu____1655 =
                                          FStar_Util.right lbname in
                                        uu____1655.FStar_Syntax_Syntax.fv_name in
                                      uu____1650.FStar_Syntax_Syntax.v in
                                    let uu____1659 =
                                      let uu____1662 =
                                        FStar_All.pipe_right quals
                                          (FStar_Util.for_some
                                             (fun uu___153_1664  ->
                                                match uu___153_1664 with
                                                | FStar_Syntax_Syntax.Projector
                                                    uu____1665 -> true
                                                | uu____1668 -> false)) in
                                      if uu____1662
                                      then
                                        let mname =
                                          let uu____1672 =
                                            mangle_projector_lid lb_lid in
                                          FStar_All.pipe_right uu____1672
                                            FStar_Extraction_ML_Syntax.mlpath_of_lident in
                                        let uu____1673 =
                                          let uu____1676 =
                                            FStar_Util.right lbname in
                                          let uu____1677 =
                                            FStar_Util.must
                                              ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc in
                                          FStar_Extraction_ML_UEnv.extend_fv'
                                            env uu____1676 mname uu____1677
                                            ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                            false in
                                        match uu____1673 with
                                        | (env1,uu____1681) ->
                                            (env1,
                                              (let uu___158_1682 = ml_lb in
                                               {
                                                 FStar_Extraction_ML_Syntax.mllb_name
                                                   =
                                                   ((snd mname),
                                                     (Prims.parse_int "0"));
                                                 FStar_Extraction_ML_Syntax.mllb_tysc
                                                   =
                                                   (uu___158_1682.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                 FStar_Extraction_ML_Syntax.mllb_add_unit
                                                   =
                                                   (uu___158_1682.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                 FStar_Extraction_ML_Syntax.mllb_def
                                                   =
                                                   (uu___158_1682.FStar_Extraction_ML_Syntax.mllb_def);
                                                 FStar_Extraction_ML_Syntax.print_typ
                                                   =
                                                   (uu___158_1682.FStar_Extraction_ML_Syntax.print_typ)
                                               }))
                                      else
                                        (let uu____1685 =
                                           let uu____1686 =
                                             let uu____1689 =
                                               FStar_Util.must
                                                 ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc in
                                             FStar_Extraction_ML_UEnv.extend_lb
                                               env lbname t uu____1689
                                               ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                               false in
                                           FStar_All.pipe_left
                                             FStar_Pervasives.fst uu____1686 in
                                         (uu____1685, ml_lb)) in
                                    (match uu____1659 with
                                     | (g1,ml_lb1) ->
                                         (g1, (ml_lb1 :: ml_lbs)))) (g, [])
                         bindings (snd lbs) in
                     (match uu____1611 with
                      | (g1,ml_lbs') ->
                          let flags =
                            FStar_List.choose
                              (fun uu___154_1709  ->
                                 match uu___154_1709 with
                                 | FStar_Syntax_Syntax.Assumption  ->
                                     Some FStar_Extraction_ML_Syntax.Assumed
                                 | FStar_Syntax_Syntax.Private  ->
                                     Some FStar_Extraction_ML_Syntax.Private
                                 | FStar_Syntax_Syntax.NoExtract  ->
                                     Some
                                       FStar_Extraction_ML_Syntax.NoExtract
                                 | uu____1711 -> None) quals in
                          let flags' =
                            FStar_List.choose
                              (fun uu___155_1716  ->
                                 match uu___155_1716 with
                                 | {
                                     FStar_Syntax_Syntax.n =
                                       FStar_Syntax_Syntax.Tm_constant
                                       (FStar_Const.Const_string
                                       (data,uu____1721));
                                     FStar_Syntax_Syntax.tk = uu____1722;
                                     FStar_Syntax_Syntax.pos = uu____1723;
                                     FStar_Syntax_Syntax.vars = uu____1724;_}
                                     ->
                                     Some
                                       (FStar_Extraction_ML_Syntax.Attribute
                                          (FStar_Util.string_of_unicode data))
                                 | uu____1729 ->
                                     (FStar_Util.print_warning
                                        "Warning: unrecognized, non-string attribute, bother protz for a better error message";
                                      None)) attrs in
                          let uu____1733 =
                            let uu____1735 =
                              let uu____1737 =
                                let uu____1738 =
                                  FStar_Extraction_ML_Util.mlloc_of_range
                                    se.FStar_Syntax_Syntax.sigrng in
                                FStar_Extraction_ML_Syntax.MLM_Loc uu____1738 in
                              [uu____1737;
                              FStar_Extraction_ML_Syntax.MLM_Let
                                (flavor, (FStar_List.append flags flags'),
                                  (FStar_List.rev ml_lbs'))] in
                            FStar_List.append uu____1735
                              tactic_registration_decl in
                          (g1, uu____1733))
                 | uu____1742 ->
                     let uu____1743 =
                       let uu____1744 =
                         FStar_Extraction_ML_Code.string_of_mlexpr
                           g.FStar_Extraction_ML_UEnv.currentModule ml_let in
                       FStar_Util.format1
                         "Impossible: Translated a let to a non-let: %s"
                         uu____1744 in
                     failwith uu____1743))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____1749,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____1753 =
             FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption) in
           if uu____1753
           then
             let always_fail =
               let imp =
                 let uu____1760 = FStar_Syntax_Util.arrow_formals t in
                 match uu____1760 with
                 | ([],t1) ->
                     let b =
                       let uu____1779 =
                         FStar_Syntax_Syntax.gen_bv "_" None t1 in
                       FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                         uu____1779 in
                     let uu____1780 = fail_exp lid t1 in
                     FStar_Syntax_Util.abs [b] uu____1780 None
                 | (bs,t1) ->
                     let uu____1793 = fail_exp lid t1 in
                     FStar_Syntax_Util.abs bs uu____1793 None in
               let uu___159_1794 = se in
               let uu____1795 =
                 let uu____1796 =
                   let uu____1802 =
                     let uu____1806 =
                       let uu____1808 =
                         let uu____1809 =
                           let uu____1812 =
                             FStar_Syntax_Syntax.lid_as_fv lid
                               FStar_Syntax_Syntax.Delta_constant None in
                           FStar_Util.Inr uu____1812 in
                         {
                           FStar_Syntax_Syntax.lbname = uu____1809;
                           FStar_Syntax_Syntax.lbunivs = [];
                           FStar_Syntax_Syntax.lbtyp = t;
                           FStar_Syntax_Syntax.lbeff =
                             FStar_Syntax_Const.effect_ML_lid;
                           FStar_Syntax_Syntax.lbdef = imp
                         } in
                       [uu____1808] in
                     (false, uu____1806) in
                   (uu____1802, [], []) in
                 FStar_Syntax_Syntax.Sig_let uu____1796 in
               {
                 FStar_Syntax_Syntax.sigel = uu____1795;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___159_1794.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___159_1794.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___159_1794.FStar_Syntax_Syntax.sigmeta)
               } in
             let uu____1819 = extract_sig g always_fail in
             (match uu____1819 with
              | (g1,mlm) ->
                  let uu____1830 =
                    FStar_Util.find_map quals
                      (fun uu___156_1832  ->
                         match uu___156_1832 with
                         | FStar_Syntax_Syntax.Discriminator l -> Some l
                         | uu____1835 -> None) in
                  (match uu____1830 with
                   | Some l ->
                       let uu____1840 =
                         let uu____1842 =
                           let uu____1843 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____1843 in
                         let uu____1844 =
                           let uu____1846 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l in
                           [uu____1846] in
                         uu____1842 :: uu____1844 in
                       (g1, uu____1840)
                   | uu____1848 ->
                       let uu____1850 =
                         FStar_Util.find_map quals
                           (fun uu___157_1852  ->
                              match uu___157_1852 with
                              | FStar_Syntax_Syntax.Projector (l,uu____1855)
                                  -> Some l
                              | uu____1856 -> None) in
                       (match uu____1850 with
                        | Some uu____1860 -> (g1, [])
                        | uu____1862 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____1868 = FStar_Extraction_ML_Term.term_as_mlexpr g e in
           (match uu____1868 with
            | (ml_main,uu____1876,uu____1877) ->
                let uu____1878 =
                  let uu____1880 =
                    let uu____1881 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____1881 in
                  [uu____1880; FStar_Extraction_ML_Syntax.MLM_Top ml_main] in
                (g, uu____1878))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____1883 ->
           failwith "impossible -- removed by tc.fs"
       | FStar_Syntax_Syntax.Sig_assume uu____1887 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____1891 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____1893 -> (g, [])
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (if p = FStar_Syntax_Syntax.LightOff
            then FStar_Options.set_ml_ish ()
            else ();
            (g, [])))
let extract_iface:
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.modul -> env_t =
  fun g  ->
    fun m  ->
      let uu____1913 =
        FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____1913 FStar_Pervasives.fst
let extract:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Extraction_ML_UEnv.env* FStar_Extraction_ML_Syntax.mllib
        Prims.list)
  =
  fun g  ->
    fun m  ->
      FStar_Syntax_Syntax.reset_gensym ();
      (let uu____1941 = FStar_Options.debug_any () in
       if uu____1941
       then
         let uu____1942 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
         FStar_Util.print1 "Extracting module %s\n" uu____1942
       else ());
      (let uu____1944 = FStar_Options.restore_cmd_line_options true in
       let name =
         FStar_Extraction_ML_Syntax.mlpath_of_lident
           m.FStar_Syntax_Syntax.name in
       let g1 =
         let uu___160_1947 = g in
         {
           FStar_Extraction_ML_UEnv.tcenv =
             (uu___160_1947.FStar_Extraction_ML_UEnv.tcenv);
           FStar_Extraction_ML_UEnv.gamma =
             (uu___160_1947.FStar_Extraction_ML_UEnv.gamma);
           FStar_Extraction_ML_UEnv.tydefs =
             (uu___160_1947.FStar_Extraction_ML_UEnv.tydefs);
           FStar_Extraction_ML_UEnv.currentModule = name
         } in
       let uu____1948 =
         FStar_Util.fold_map extract_sig g1
           m.FStar_Syntax_Syntax.declarations in
       match uu____1948 with
       | (g2,sigs) ->
           let mlm = FStar_List.flatten sigs in
           let is_kremlin =
             let uu____1965 = FStar_Options.codegen () in
             match uu____1965 with
             | Some "Kremlin" -> true
             | uu____1967 -> false in
           let uu____1969 =
             (((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
                (is_kremlin ||
                   (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)))
               &&
               (FStar_Options.should_extract
                  (m.FStar_Syntax_Syntax.name).FStar_Ident.str) in
           if uu____1969
           then
             ((let uu____1974 =
                 FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
               FStar_Util.print1 "Extracted module %s\n" uu____1974);
              (g2,
                [FStar_Extraction_ML_Syntax.MLLib
                   [(name, (Some ([], mlm)),
                      (FStar_Extraction_ML_Syntax.MLLib []))]]))
           else (g2, []))