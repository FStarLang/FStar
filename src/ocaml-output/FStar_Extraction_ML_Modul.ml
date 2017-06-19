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
let as_pair uu___148_88 =
  match uu___148_88 with
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
            | uu____191 -> def1 in
          let uu____192 =
            match def2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____199) ->
                FStar_Syntax_Subst.open_term bs body
            | uu____222 -> ([], def2) in
          match uu____192 with
          | (bs,body) ->
              let assumed =
                FStar_Util.for_some
                  (fun uu___149_234  ->
                     match uu___149_234 with
                     | FStar_Syntax_Syntax.Assumption  -> true
                     | uu____235 -> false) quals in
              let uu____236 = binders_as_mlty_binders env bs in
              (match uu____236 with
               | (env1,ml_bs) ->
                   let body1 =
                     let uu____254 =
                       FStar_Extraction_ML_Term.term_as_mlty env1 body in
                     FStar_All.pipe_right uu____254
                       (FStar_Extraction_ML_Util.eraseTypeDeep
                          (FStar_Extraction_ML_Util.udelta_unfold env1)) in
                   let mangled_projector =
                     let uu____257 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___150_259  ->
                               match uu___150_259 with
                               | FStar_Syntax_Syntax.Projector uu____260 ->
                                   true
                               | uu____263 -> false)) in
                     if uu____257
                     then
                       let mname = mangle_projector_lid lid in
                       Some ((mname.FStar_Ident.ident).FStar_Ident.idText)
                     else None in
                   let td =
                     let uu____279 =
                       let uu____290 = lident_as_mlsymbol lid in
                       (assumed, uu____290, mangled_projector, ml_bs,
                         (Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1))) in
                     [uu____279] in
                   let def3 =
                     let uu____318 =
                       let uu____319 =
                         FStar_Extraction_ML_Util.mlloc_of_range
                           (FStar_Ident.range_of_lid lid) in
                       FStar_Extraction_ML_Syntax.MLM_Loc uu____319 in
                     [uu____318; FStar_Extraction_ML_Syntax.MLM_Ty td] in
                   let env2 =
                     let uu____321 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___151_323  ->
                               match uu___151_323 with
                               | FStar_Syntax_Syntax.Assumption  -> true
                               | FStar_Syntax_Syntax.New  -> true
                               | uu____324 -> false)) in
                     if uu____321
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
    let uu____432 = FStar_Syntax_Print.lid_to_string i.iname in
    let uu____433 = FStar_Syntax_Print.binders_to_string " " i.iparams in
    let uu____434 = FStar_Syntax_Print.term_to_string i.ityp in
    let uu____435 =
      let uu____436 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let uu____441 = FStar_Syntax_Print.lid_to_string d.dname in
                let uu____442 =
                  let uu____443 = FStar_Syntax_Print.term_to_string d.dtyp in
                  Prims.strcat " : " uu____443 in
                Prims.strcat uu____441 uu____442)) in
      FStar_All.pipe_right uu____436 (FStar_String.concat "\n\t\t") in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____432 uu____433 uu____434
      uu____435
let bundle_as_inductive_families env ses quals =
  FStar_All.pipe_right ses
    (FStar_List.collect
       (fun se  ->
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_inductive_typ (l,_us,bs,t,_mut_i,datas)
              ->
              let uu____486 = FStar_Syntax_Subst.open_term bs t in
              (match uu____486 with
               | (bs1,t1) ->
                   let datas1 =
                     FStar_All.pipe_right ses
                       (FStar_List.collect
                          (fun se1  ->
                             match se1.FStar_Syntax_Syntax.sigel with
                             | FStar_Syntax_Syntax.Sig_datacon
                                 (d,uu____499,t2,l',nparams,uu____503) when
                                 FStar_Ident.lid_equals l l' ->
                                 let uu____506 =
                                   FStar_Syntax_Util.arrow_formals t2 in
                                 (match uu____506 with
                                  | (bs',body) ->
                                      let uu____527 =
                                        FStar_Util.first_N
                                          (FStar_List.length bs1) bs' in
                                      (match uu____527 with
                                       | (bs_params,rest) ->
                                           let subst1 =
                                             FStar_List.map2
                                               (fun uu____565  ->
                                                  fun uu____566  ->
                                                    match (uu____565,
                                                            uu____566)
                                                    with
                                                    | ((b',uu____576),
                                                       (b,uu____578)) ->
                                                        let uu____583 =
                                                          let uu____588 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              b in
                                                          (b', uu____588) in
                                                        FStar_Syntax_Syntax.NT
                                                          uu____583)
                                               bs_params bs1 in
                                           let t3 =
                                             let uu____590 =
                                               let uu____593 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   body in
                                               FStar_Syntax_Util.arrow rest
                                                 uu____593 in
                                             FStar_All.pipe_right uu____590
                                               (FStar_Syntax_Subst.subst
                                                  subst1) in
                                           [{ dname = d; dtyp = t3 }]))
                             | uu____598 -> [])) in
                   [{
                      iname = l;
                      iparams = bs1;
                      ityp = t1;
                      idatas = datas1;
                      iquals = (se.FStar_Syntax_Syntax.sigquals)
                    }])
          | uu____599 -> []))
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
          let uu____642 =
            FStar_Extraction_ML_Term.term_as_mlty env1 ctor.dtyp in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env1) uu____642 in
        let steps =
          [FStar_TypeChecker_Normalize.Inlining;
          FStar_TypeChecker_Normalize.UnfoldUntil
            FStar_Syntax_Syntax.Delta_constant;
          FStar_TypeChecker_Normalize.EraseUniverses;
          FStar_TypeChecker_Normalize.AllowUnboundUniverses] in
        let names1 =
          let uu____647 =
            let uu____648 =
              let uu____651 =
                FStar_TypeChecker_Normalize.normalize steps
                  env1.FStar_Extraction_ML_UEnv.tcenv ctor.dtyp in
              FStar_Syntax_Subst.compress uu____651 in
            uu____648.FStar_Syntax_Syntax.n in
          match uu____647 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,uu____654) ->
              FStar_List.map
                (fun uu____667  ->
                   match uu____667 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____671;
                        FStar_Syntax_Syntax.sort = uu____672;_},uu____673)
                       -> ppname.FStar_Ident.idText) bs
          | uu____676 -> [] in
        let tys = (ml_tyvars, mlt) in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp in
        let uu____687 =
          let uu____688 =
            FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false in
          fst uu____688 in
        let uu____691 =
          let uu____697 = lident_as_mlsymbol ctor.dname in
          let uu____698 =
            let uu____702 = FStar_Extraction_ML_Util.argTypes mlt in
            FStar_List.zip names1 uu____702 in
          (uu____697, uu____698) in
        (uu____687, uu____691) in
      let extract_one_family env1 ind =
        let uu____731 = binders_as_mlty_binders env1 ind.iparams in
        match uu____731 with
        | (env2,vars) ->
            let uu____757 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor vars) env2) in
            (match uu____757 with
             | (env3,ctors) ->
                 let uu____806 = FStar_Syntax_Util.arrow_formals ind.ityp in
                 (match uu____806 with
                  | (indices,uu____827) ->
                      let ml_params =
                        let uu____842 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____857  ->
                                    let uu____860 =
                                      let uu____861 =
                                        FStar_Util.string_of_int i in
                                      Prims.strcat "'dummyV" uu____861 in
                                    (uu____860, (Prims.parse_int "0")))) in
                        FStar_List.append vars uu____842 in
                      let tbody =
                        let uu____865 =
                          FStar_Util.find_opt
                            (fun uu___152_867  ->
                               match uu___152_867 with
                               | FStar_Syntax_Syntax.RecordType uu____868 ->
                                   true
                               | uu____873 -> false) ind.iquals in
                        match uu____865 with
                        | Some (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____880 = FStar_List.hd ctors in
                            (match uu____880 with
                             | (uu____891,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id  ->
                                        fun uu____909  ->
                                          match uu____909 with
                                          | (uu____914,ty) ->
                                              let lid =
                                                FStar_Ident.lid_of_ids
                                                  (FStar_List.append ns [id]) in
                                              let uu____917 =
                                                lident_as_mlsymbol lid in
                                              (uu____917, ty)) ids c_ty in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____918 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors in
                      let uu____920 =
                        let uu____931 = lident_as_mlsymbol ind.iname in
                        (false, uu____931, None, ml_params, (Some tbody)) in
                      (env3, uu____920))) in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____952,t,uu____954,uu____955,uu____956);
            FStar_Syntax_Syntax.sigrng = uu____957;
            FStar_Syntax_Syntax.sigquals = uu____958;
            FStar_Syntax_Syntax.sigmeta = uu____959;_}::[],uu____960),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____968 = extract_ctor [] env { dname = l; dtyp = t } in
          (match uu____968 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____995),quals) ->
          let ifams = bundle_as_inductive_families env ses quals in
          let uu____1006 = FStar_Util.fold_map extract_one_family env ifams in
          (match uu____1006 with
           | (env1,td) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Ty td]))
      | uu____1058 -> failwith "Unexpected signature element"
let rec extract_sig:
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t* FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
  =
  fun g  ->
    fun se  ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u  ->
           let uu____1081 = FStar_Syntax_Print.sigelt_to_string se in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____1081);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____1085 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____1090 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____1099 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
           ->
           let extend_env g1 lid ml_name tm tysc =
             let uu____1127 =
               let uu____1130 =
                 FStar_Syntax_Syntax.lid_as_fv lid
                   FStar_Syntax_Syntax.Delta_equational None in
               FStar_Extraction_ML_UEnv.extend_fv' g1 uu____1130 ml_name tysc
                 false false in
             match uu____1127 with
             | (g2,mangled_name) ->
                 ((let uu____1136 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          g2.FStar_Extraction_ML_UEnv.tcenv)
                       (FStar_Options.Other "ExtractionReify") in
                   if uu____1136
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
             (let uu____1148 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify") in
              if uu____1148
              then
                let uu____1149 = FStar_Syntax_Print.term_to_string tm in
                FStar_Util.print1 "extract_fv term: %s\n" uu____1149
              else ());
             (let uu____1151 =
                let uu____1152 = FStar_Syntax_Subst.compress tm in
                uu____1152.FStar_Syntax_Syntax.n in
              match uu____1151 with
              | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____1158) ->
                  extract_fv tm1
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let mlp =
                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  let uu____1169 =
                    let uu____1174 = FStar_Extraction_ML_UEnv.lookup_fv g fv in
                    FStar_All.pipe_left FStar_Util.right uu____1174 in
                  (match uu____1169 with
                   | (uu____1203,uu____1204,tysc,uu____1206) ->
                       let uu____1207 =
                         FStar_All.pipe_left
                           (FStar_Extraction_ML_Syntax.with_ty
                              FStar_Extraction_ML_Syntax.MLTY_Top)
                           (FStar_Extraction_ML_Syntax.MLE_Name mlp) in
                       (uu____1207, tysc))
              | uu____1208 -> failwith "Not an fv") in
           let extract_action g1 a =
             (let uu____1230 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g1.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify") in
              if uu____1230
              then
                let uu____1231 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_typ in
                let uu____1232 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_defn in
                FStar_Util.print2 "Action type %s and term %s\n" uu____1231
                  uu____1232
              else ());
             (let uu____1234 = FStar_Extraction_ML_UEnv.action_name ed a in
              match uu____1234 with
              | (a_nm,a_lid) ->
                  let lbname =
                    let uu____1244 =
                      FStar_Syntax_Syntax.new_bv
                        (Some
                           ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                        FStar_Syntax_Syntax.tun in
                    FStar_Util.Inl uu____1244 in
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
                  let uu____1267 =
                    FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb in
                  (match uu____1267 with
                   | (a_let,uu____1274,ty) ->
                       ((let uu____1277 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug
                                g1.FStar_Extraction_ML_UEnv.tcenv)
                             (FStar_Options.Other "ExtractionReify") in
                         if uu____1277
                         then
                           let uu____1278 =
                             FStar_Extraction_ML_Code.string_of_mlexpr a_nm
                               a_let in
                           FStar_Util.print1 "Extracted action term: %s\n"
                             uu____1278
                         else ());
                        (let uu____1280 =
                           match a_let.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_Let
                               ((uu____1285,uu____1286,mllb::[]),uu____1288)
                               ->
                               (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                                with
                                | Some tysc ->
                                    ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                      tysc)
                                | None  -> failwith "No type scheme")
                           | uu____1299 -> failwith "Impossible" in
                         match uu____1280 with
                         | (exp,tysc) ->
                             ((let uu____1307 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug
                                      g1.FStar_Extraction_ML_UEnv.tcenv)
                                   (FStar_Options.Other "ExtractionReify") in
                               if uu____1307
                               then
                                 ((let uu____1309 =
                                     FStar_Extraction_ML_Code.string_of_mlty
                                       a_nm (snd tysc) in
                                   FStar_Util.print1
                                     "Extracted action type: %s\n" uu____1309);
                                  FStar_List.iter
                                    (fun x  ->
                                       FStar_Util.print1 "and binders: %s\n"
                                         (fst x)) (fst tysc))
                               else ());
                              extend_env g1 a_lid a_nm exp tysc))))) in
           let uu____1316 =
             let uu____1319 =
               extract_fv (snd ed.FStar_Syntax_Syntax.return_repr) in
             match uu____1319 with
             | (return_tm,ty_sc) ->
                 let uu____1327 =
                   FStar_Extraction_ML_UEnv.monad_op_name ed "return" in
                 (match uu____1327 with
                  | (return_nm,return_lid) ->
                      extend_env g return_lid return_nm return_tm ty_sc) in
           (match uu____1316 with
            | (g1,return_decl) ->
                let uu____1339 =
                  let uu____1342 =
                    extract_fv (snd ed.FStar_Syntax_Syntax.bind_repr) in
                  match uu____1342 with
                  | (bind_tm,ty_sc) ->
                      let uu____1350 =
                        FStar_Extraction_ML_UEnv.monad_op_name ed "bind" in
                      (match uu____1350 with
                       | (bind_nm,bind_lid) ->
                           extend_env g1 bind_lid bind_nm bind_tm ty_sc) in
                (match uu____1339 with
                 | (g2,bind_decl) ->
                     let uu____1362 =
                       FStar_Util.fold_map extract_action g2
                         ed.FStar_Syntax_Syntax.actions in
                     (match uu____1362 with
                      | (g3,actions) ->
                          (g3,
                            (FStar_List.append [return_decl; bind_decl]
                               actions)))))
       | FStar_Syntax_Syntax.Sig_new_effect uu____1374 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____1377,t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____1381 =
             let uu____1382 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___153_1384  ->
                       match uu___153_1384 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____1385 -> false)) in
             Prims.op_Negation uu____1382 in
           if uu____1381
           then (g, [])
           else
             (let uu____1391 = FStar_Syntax_Util.arrow_formals t in
              match uu____1391 with
              | (bs,uu____1403) ->
                  let fv =
                    FStar_Syntax_Syntax.lid_as_fv lid
                      FStar_Syntax_Syntax.Delta_constant None in
                  let uu____1415 =
                    FStar_Syntax_Util.abs bs FStar_TypeChecker_Common.t_unit
                      None in
                  extract_typ_abbrev g fv quals uu____1415)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____1422,uu____1423)
           when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____1434 =
             let uu____1439 =
               FStar_TypeChecker_Env.open_universes_in
                 g.FStar_Extraction_ML_UEnv.tcenv
                 lb.FStar_Syntax_Syntax.lbunivs
                 [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp] in
             match uu____1439 with
             | (tcenv,uu____1455,def_typ) ->
                 let uu____1459 = as_pair def_typ in (tcenv, uu____1459) in
           (match uu____1434 with
            | (tcenv,(lbdef,lbtyp)) ->
                let lbtyp1 =
                  FStar_TypeChecker_Normalize.unfold_whnf tcenv lbtyp in
                let lbdef1 =
                  FStar_TypeChecker_Normalize.eta_expand_with_type tcenv
                    lbdef lbtyp1 in
                let uu____1474 =
                  FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                extract_typ_abbrev g uu____1474 quals lbdef1)
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____1476,attrs) ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let elet =
             FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_let
                  (lbs, FStar_Syntax_Const.exp_false_bool)) None
               se.FStar_Syntax_Syntax.sigrng in
           let tactic_registration_decl =
             let is_tactic_decl tac_lid h =
               match h.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_uinst (h',uu____1501) ->
                   let uu____1506 =
                     let uu____1507 = FStar_Syntax_Subst.compress h' in
                     uu____1507.FStar_Syntax_Syntax.n in
                   (match uu____1506 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Syntax_Const.tactic_lid
                        ->
                        let uu____1511 =
                          let uu____1512 =
                            FStar_Extraction_ML_Syntax.string_of_mlpath
                              g.FStar_Extraction_ML_UEnv.currentModule in
                          FStar_Util.starts_with uu____1512 "FStar.Tactics" in
                        Prims.op_Negation uu____1511
                    | uu____1513 -> false)
               | uu____1514 -> false in
             let mk_registration tac_lid assm_lid t bs =
               let h =
                 let uu____1539 =
                   let uu____1540 =
                     let uu____1541 =
                       FStar_Ident.lid_of_str
                         "FStar_Tactics_Native.register_tactic" in
                     FStar_Extraction_ML_Syntax.mlpath_of_lident uu____1541 in
                   FStar_Extraction_ML_Syntax.MLE_Name uu____1540 in
                 FStar_All.pipe_left
                   (FStar_Extraction_ML_Syntax.with_ty
                      FStar_Extraction_ML_Syntax.MLTY_Top) uu____1539 in
               let lid_arg =
                 let uu____1543 =
                   let uu____1544 = FStar_Ident.string_of_lid assm_lid in
                   FStar_Extraction_ML_Syntax.MLC_String uu____1544 in
                 FStar_Extraction_ML_Syntax.MLE_Const uu____1543 in
               let tac_arity = FStar_List.length bs in
               let arity =
                 let uu____1551 =
                   let uu____1552 =
                     let uu____1553 =
                       FStar_Util.string_of_int
                         (tac_arity + (Prims.parse_int "1")) in
                     FStar_Ident.lid_of_str uu____1553 in
                   FStar_Extraction_ML_Syntax.mlpath_of_lident uu____1552 in
                 FStar_Extraction_ML_Syntax.MLE_Name uu____1551 in
               let tac_interpretation =
                 FStar_Extraction_ML_Util.mk_interpretation_fun tac_lid
                   lid_arg t bs in
               let app =
                 let uu____1562 =
                   let uu____1563 =
                     let uu____1567 =
                       FStar_List.map
                         (FStar_Extraction_ML_Syntax.with_ty
                            FStar_Extraction_ML_Syntax.MLTY_Top)
                         [lid_arg; arity; tac_interpretation] in
                     (h, uu____1567) in
                   FStar_Extraction_ML_Syntax.MLE_App uu____1563 in
                 FStar_All.pipe_left
                   (FStar_Extraction_ML_Syntax.with_ty
                      FStar_Extraction_ML_Syntax.MLTY_Top) uu____1562 in
               FStar_Extraction_ML_Syntax.MLM_Top app in
             match snd lbs with
             | hd1::[] ->
                 let uu____1573 =
                   FStar_Syntax_Util.arrow_formals_comp
                     hd1.FStar_Syntax_Syntax.lbtyp in
                 (match uu____1573 with
                  | (bs,comp) ->
                      let t = FStar_Syntax_Util.comp_result comp in
                      let uu____1591 =
                        let uu____1592 = FStar_Syntax_Subst.compress t in
                        uu____1592.FStar_Syntax_Syntax.n in
                      (match uu____1591 with
                       | FStar_Syntax_Syntax.Tm_app (h,args) ->
                           let h1 = FStar_Syntax_Subst.compress h in
                           let tac_lid =
                             let uu____1614 =
                               let uu____1619 =
                                 FStar_Util.right
                                   hd1.FStar_Syntax_Syntax.lbname in
                               uu____1619.FStar_Syntax_Syntax.fv_name in
                             uu____1614.FStar_Syntax_Syntax.v in
                           let assm_lid =
                             let uu____1624 =
                               FStar_All.pipe_left FStar_Ident.id_of_text
                                 (Prims.strcat "__"
                                    (tac_lid.FStar_Ident.ident).FStar_Ident.idText) in
                             FStar_Ident.lid_of_ns_and_id
                               tac_lid.FStar_Ident.ns uu____1624 in
                           let uu____1625 = is_tactic_decl assm_lid h1 in
                           if uu____1625
                           then
                             let uu____1627 =
                               let uu____1628 =
                                 let uu____1631 = FStar_List.hd args in
                                 fst uu____1631 in
                               mk_registration tac_lid assm_lid uu____1628 bs in
                             [uu____1627]
                           else []
                       | uu____1643 -> []))
             | uu____1644 -> [] in
           let uu____1646 = FStar_Extraction_ML_Term.term_as_mlexpr g elet in
           (match uu____1646 with
            | (ml_let,uu____1654,uu____1655) ->
                (match ml_let.FStar_Extraction_ML_Syntax.expr with
                 | FStar_Extraction_ML_Syntax.MLE_Let
                     ((flavor,uu____1660,bindings),uu____1662) ->
                     let uu____1669 =
                       FStar_List.fold_left2
                         (fun uu____1676  ->
                            fun ml_lb  ->
                              fun uu____1678  ->
                                match (uu____1676, uu____1678) with
                                | ((env,ml_lbs),{
                                                  FStar_Syntax_Syntax.lbname
                                                    = lbname;
                                                  FStar_Syntax_Syntax.lbunivs
                                                    = uu____1691;
                                                  FStar_Syntax_Syntax.lbtyp =
                                                    t;
                                                  FStar_Syntax_Syntax.lbeff =
                                                    uu____1693;
                                                  FStar_Syntax_Syntax.lbdef =
                                                    uu____1694;_})
                                    ->
                                    let lb_lid =
                                      let uu____1708 =
                                        let uu____1713 =
                                          FStar_Util.right lbname in
                                        uu____1713.FStar_Syntax_Syntax.fv_name in
                                      uu____1708.FStar_Syntax_Syntax.v in
                                    let uu____1717 =
                                      let uu____1720 =
                                        FStar_All.pipe_right quals
                                          (FStar_Util.for_some
                                             (fun uu___154_1722  ->
                                                match uu___154_1722 with
                                                | FStar_Syntax_Syntax.Projector
                                                    uu____1723 -> true
                                                | uu____1726 -> false)) in
                                      if uu____1720
                                      then
                                        let mname =
                                          let uu____1730 =
                                            mangle_projector_lid lb_lid in
                                          FStar_All.pipe_right uu____1730
                                            FStar_Extraction_ML_Syntax.mlpath_of_lident in
                                        let uu____1731 =
                                          let uu____1734 =
                                            FStar_Util.right lbname in
                                          let uu____1735 =
                                            FStar_Util.must
                                              ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc in
                                          FStar_Extraction_ML_UEnv.extend_fv'
                                            env uu____1734 mname uu____1735
                                            ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                            false in
                                        match uu____1731 with
                                        | (env1,uu____1739) ->
                                            (env1,
                                              (let uu___159_1740 = ml_lb in
                                               {
                                                 FStar_Extraction_ML_Syntax.mllb_name
                                                   =
                                                   ((snd mname),
                                                     (Prims.parse_int "0"));
                                                 FStar_Extraction_ML_Syntax.mllb_tysc
                                                   =
                                                   (uu___159_1740.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                 FStar_Extraction_ML_Syntax.mllb_add_unit
                                                   =
                                                   (uu___159_1740.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                 FStar_Extraction_ML_Syntax.mllb_def
                                                   =
                                                   (uu___159_1740.FStar_Extraction_ML_Syntax.mllb_def);
                                                 FStar_Extraction_ML_Syntax.print_typ
                                                   =
                                                   (uu___159_1740.FStar_Extraction_ML_Syntax.print_typ)
                                               }))
                                      else
                                        (let uu____1743 =
                                           let uu____1744 =
                                             let uu____1747 =
                                               FStar_Util.must
                                                 ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc in
                                             FStar_Extraction_ML_UEnv.extend_lb
                                               env lbname t uu____1747
                                               ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                               false in
                                           FStar_All.pipe_left
                                             FStar_Pervasives.fst uu____1744 in
                                         (uu____1743, ml_lb)) in
                                    (match uu____1717 with
                                     | (g1,ml_lb1) ->
                                         (g1, (ml_lb1 :: ml_lbs)))) (g, [])
                         bindings (snd lbs) in
                     (match uu____1669 with
                      | (g1,ml_lbs') ->
                          let flags =
                            FStar_List.choose
                              (fun uu___155_1767  ->
                                 match uu___155_1767 with
                                 | FStar_Syntax_Syntax.Assumption  ->
                                     Some FStar_Extraction_ML_Syntax.Assumed
                                 | FStar_Syntax_Syntax.Private  ->
                                     Some FStar_Extraction_ML_Syntax.Private
                                 | FStar_Syntax_Syntax.NoExtract  ->
                                     Some
                                       FStar_Extraction_ML_Syntax.NoExtract
                                 | uu____1769 -> None) quals in
                          let flags' =
                            FStar_List.choose
                              (fun uu___156_1774  ->
                                 match uu___156_1774 with
                                 | {
                                     FStar_Syntax_Syntax.n =
                                       FStar_Syntax_Syntax.Tm_constant
                                       (FStar_Const.Const_string
                                       (data,uu____1779));
                                     FStar_Syntax_Syntax.tk = uu____1780;
                                     FStar_Syntax_Syntax.pos = uu____1781;
                                     FStar_Syntax_Syntax.vars = uu____1782;_}
                                     ->
                                     Some
                                       (FStar_Extraction_ML_Syntax.Attribute
                                          (FStar_Util.string_of_unicode data))
                                 | uu____1787 ->
                                     (FStar_Util.print_warning
                                        "Warning: unrecognized, non-string attribute, bother protz for a better error message";
                                      None)) attrs in
                          let uu____1791 =
                            let uu____1793 =
                              let uu____1795 =
                                let uu____1796 =
                                  FStar_Extraction_ML_Util.mlloc_of_range
                                    se.FStar_Syntax_Syntax.sigrng in
                                FStar_Extraction_ML_Syntax.MLM_Loc uu____1796 in
                              [uu____1795;
                              FStar_Extraction_ML_Syntax.MLM_Let
                                (flavor, (FStar_List.append flags flags'),
                                  (FStar_List.rev ml_lbs'))] in
                            FStar_List.append uu____1793
                              tactic_registration_decl in
                          (g1, uu____1791))
                 | uu____1800 ->
                     let uu____1801 =
                       let uu____1802 =
                         FStar_Extraction_ML_Code.string_of_mlexpr
                           g.FStar_Extraction_ML_UEnv.currentModule ml_let in
                       FStar_Util.format1
                         "Impossible: Translated a let to a non-let: %s"
                         uu____1802 in
                     failwith uu____1801))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____1807,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____1811 =
             FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption) in
           if uu____1811
           then
             let always_fail =
               let imp =
                 let uu____1818 = FStar_Syntax_Util.arrow_formals t in
                 match uu____1818 with
                 | ([],t1) ->
                     let b =
                       let uu____1837 =
                         FStar_Syntax_Syntax.gen_bv "_" None t1 in
                       FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                         uu____1837 in
                     let uu____1838 = fail_exp lid t1 in
                     FStar_Syntax_Util.abs [b] uu____1838 None
                 | (bs,t1) ->
                     let uu____1856 = fail_exp lid t1 in
                     FStar_Syntax_Util.abs bs uu____1856 None in
               let uu___160_1862 = se in
               let uu____1863 =
                 let uu____1864 =
                   let uu____1870 =
                     let uu____1874 =
                       let uu____1876 =
                         let uu____1877 =
                           let uu____1880 =
                             FStar_Syntax_Syntax.lid_as_fv lid
                               FStar_Syntax_Syntax.Delta_constant None in
                           FStar_Util.Inr uu____1880 in
                         {
                           FStar_Syntax_Syntax.lbname = uu____1877;
                           FStar_Syntax_Syntax.lbunivs = [];
                           FStar_Syntax_Syntax.lbtyp = t;
                           FStar_Syntax_Syntax.lbeff =
                             FStar_Syntax_Const.effect_ML_lid;
                           FStar_Syntax_Syntax.lbdef = imp
                         } in
                       [uu____1876] in
                     (false, uu____1874) in
                   (uu____1870, [], []) in
                 FStar_Syntax_Syntax.Sig_let uu____1864 in
               {
                 FStar_Syntax_Syntax.sigel = uu____1863;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___160_1862.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___160_1862.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___160_1862.FStar_Syntax_Syntax.sigmeta)
               } in
             let uu____1887 = extract_sig g always_fail in
             (match uu____1887 with
              | (g1,mlm) ->
                  let uu____1898 =
                    FStar_Util.find_map quals
                      (fun uu___157_1900  ->
                         match uu___157_1900 with
                         | FStar_Syntax_Syntax.Discriminator l -> Some l
                         | uu____1903 -> None) in
                  (match uu____1898 with
                   | Some l ->
                       let uu____1908 =
                         let uu____1910 =
                           let uu____1911 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____1911 in
                         let uu____1912 =
                           let uu____1914 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l in
                           [uu____1914] in
                         uu____1910 :: uu____1912 in
                       (g1, uu____1908)
                   | uu____1916 ->
                       let uu____1918 =
                         FStar_Util.find_map quals
                           (fun uu___158_1920  ->
                              match uu___158_1920 with
                              | FStar_Syntax_Syntax.Projector (l,uu____1923)
                                  -> Some l
                              | uu____1924 -> None) in
                       (match uu____1918 with
                        | Some uu____1928 -> (g1, [])
                        | uu____1930 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____1936 = FStar_Extraction_ML_Term.term_as_mlexpr g e in
           (match uu____1936 with
            | (ml_main,uu____1944,uu____1945) ->
                let uu____1946 =
                  let uu____1948 =
                    let uu____1949 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____1949 in
                  [uu____1948; FStar_Extraction_ML_Syntax.MLM_Top ml_main] in
                (g, uu____1946))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____1951 ->
           failwith "impossible -- removed by tc.fs"
       | FStar_Syntax_Syntax.Sig_assume uu____1955 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____1959 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____1961 -> (g, [])
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (if p = FStar_Syntax_Syntax.LightOff
            then FStar_Options.set_ml_ish ()
            else ();
            (g, [])))
let extract_iface:
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.modul -> env_t =
  fun g  ->
    fun m  ->
      let uu____1981 =
        FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____1981 FStar_Pervasives.fst
let extract:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Extraction_ML_UEnv.env* FStar_Extraction_ML_Syntax.mllib
        Prims.list)
  =
  fun g  ->
    fun m  ->
      FStar_Syntax_Syntax.reset_gensym ();
      (let uu____2009 = FStar_Options.debug_any () in
       if uu____2009
       then
         let uu____2010 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
         FStar_Util.print1 "Extracting module %s\n" uu____2010
       else ());
      (let uu____2012 = FStar_Options.restore_cmd_line_options true in
       let name =
         FStar_Extraction_ML_Syntax.mlpath_of_lident
           m.FStar_Syntax_Syntax.name in
       let g1 =
         let uu___161_2015 = g in
         {
           FStar_Extraction_ML_UEnv.tcenv =
             (uu___161_2015.FStar_Extraction_ML_UEnv.tcenv);
           FStar_Extraction_ML_UEnv.gamma =
             (uu___161_2015.FStar_Extraction_ML_UEnv.gamma);
           FStar_Extraction_ML_UEnv.tydefs =
             (uu___161_2015.FStar_Extraction_ML_UEnv.tydefs);
           FStar_Extraction_ML_UEnv.currentModule = name
         } in
       let uu____2016 =
         FStar_Util.fold_map extract_sig g1
           m.FStar_Syntax_Syntax.declarations in
       match uu____2016 with
       | (g2,sigs) ->
           let mlm = FStar_List.flatten sigs in
           let is_kremlin =
             let uu____2033 = FStar_Options.codegen () in
             match uu____2033 with
             | Some "Kremlin" -> true
             | uu____2035 -> false in
           let uu____2037 =
             (((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
                (is_kremlin ||
                   (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)))
               &&
               (FStar_Options.should_extract
                  (m.FStar_Syntax_Syntax.name).FStar_Ident.str) in
           if uu____2037
           then
             ((let uu____2042 =
                 FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
               FStar_Util.print1 "Extracted module %s\n" uu____2042);
              (g2,
                [FStar_Extraction_ML_Syntax.MLLib
                   [(name, (Some ([], mlm)),
                      (FStar_Extraction_ML_Syntax.MLLib []))]]))
           else (g2, []))