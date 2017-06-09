open Prims
let is_kremlin: Prims.unit -> Prims.bool =
  fun uu____3  ->
    let uu____4 = FStar_Options.codegen () in
    match uu____4 with
    | FStar_Pervasives_Native.Some "Kremlin" -> true
    | uu____6 -> false
let fail_exp lid t =
  let uu____22 =
    let uu____25 =
      let uu____26 =
        let uu____36 =
          FStar_Syntax_Syntax.fvar FStar_Parser_Const.failwith_lid
            FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None in
        let uu____37 =
          let uu____39 = FStar_Syntax_Syntax.iarg t in
          let uu____40 =
            let uu____42 =
              let uu____43 =
                let uu____44 =
                  let uu____47 =
                    let uu____48 =
                      let uu____49 =
                        let uu____53 =
                          let uu____54 =
                            let uu____55 =
                              FStar_Syntax_Print.lid_to_string lid in
                            Prims.strcat "Not yet implemented:" uu____55 in
                          FStar_Bytes.string_as_unicode_bytes uu____54 in
                        (uu____53, FStar_Range.dummyRange) in
                      FStar_Const.Const_string uu____49 in
                    FStar_Syntax_Syntax.Tm_constant uu____48 in
                  FStar_Syntax_Syntax.mk uu____47 in
                uu____44 FStar_Pervasives_Native.None FStar_Range.dummyRange in
              FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____43 in
            [uu____42] in
          uu____39 :: uu____40 in
        (uu____36, uu____37) in
      FStar_Syntax_Syntax.Tm_app uu____26 in
    FStar_Syntax_Syntax.mk uu____25 in
  uu____22 FStar_Pervasives_Native.None FStar_Range.dummyRange
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
       fun uu____124  ->
         match uu____124 with
         | (bv,uu____132) ->
             let uu____133 =
               let uu____134 =
                 let uu____136 =
                   let uu____137 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv in
                   FStar_Extraction_ML_Syntax.MLTY_Var uu____137 in
                 FStar_Pervasives_Native.Some uu____136 in
               FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____134 in
             let uu____138 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv in
             (uu____133, uu____138)) env bs
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
            let uu____166 =
              let uu____167 = FStar_Syntax_Subst.compress def in
              FStar_All.pipe_right uu____167 FStar_Syntax_Util.unmeta in
            FStar_All.pipe_right uu____166 FStar_Syntax_Util.un_uinst in
          let def2 =
            match def1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs uu____169 ->
                FStar_Extraction_ML_Term.normalize_abs def1
            | uu____184 -> def1 in
          let uu____185 =
            match def2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____192) ->
                FStar_Syntax_Subst.open_term bs body
            | uu____215 -> ([], def2) in
          match uu____185 with
          | (bs,body) ->
              let assumed =
                FStar_Util.for_some
                  (fun uu___149_227  ->
                     match uu___149_227 with
                     | FStar_Syntax_Syntax.Assumption  -> true
                     | uu____228 -> false) quals in
              let uu____229 = binders_as_mlty_binders env bs in
              (match uu____229 with
               | (env1,ml_bs) ->
                   let body1 =
                     let uu____247 =
                       FStar_Extraction_ML_Term.term_as_mlty env1 body in
                     FStar_All.pipe_right uu____247
                       (FStar_Extraction_ML_Util.eraseTypeDeep
                          (FStar_Extraction_ML_Util.udelta_unfold env1)) in
                   let mangled_projector =
                     let uu____250 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___150_252  ->
                               match uu___150_252 with
                               | FStar_Syntax_Syntax.Projector uu____253 ->
                                   true
                               | uu____256 -> false)) in
                     if uu____250
                     then
                       let mname = mangle_projector_lid lid in
                       FStar_Pervasives_Native.Some
                         ((mname.FStar_Ident.ident).FStar_Ident.idText)
                     else FStar_Pervasives_Native.None in
                   let td =
                     let uu____272 =
                       let uu____283 = lident_as_mlsymbol lid in
                       (assumed, uu____283, mangled_projector, ml_bs,
                         (FStar_Pervasives_Native.Some
                            (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1))) in
                     [uu____272] in
                   let def3 =
                     let uu____311 =
                       let uu____312 =
                         FStar_Extraction_ML_Util.mlloc_of_range
                           (FStar_Ident.range_of_lid lid) in
                       FStar_Extraction_ML_Syntax.MLM_Loc uu____312 in
                     [uu____311; FStar_Extraction_ML_Syntax.MLM_Ty td] in
                   let env2 =
                     let uu____314 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___151_316  ->
                               match uu___151_316 with
                               | FStar_Syntax_Syntax.Assumption  -> true
                               | FStar_Syntax_Syntax.New  -> true
                               | uu____317 -> false)) in
                     if uu____314
                     then env1
                     else FStar_Extraction_ML_UEnv.extend_tydef env1 fv td in
                   (env2, def3))
type data_constructor =
  {
  dname: FStar_Ident.lident;
  dtyp: FStar_Syntax_Syntax.typ;}
type inductive_family =
  {
  iname: FStar_Ident.lident;
  iparams: FStar_Syntax_Syntax.binders;
  ityp: FStar_Syntax_Syntax.term;
  idatas: data_constructor Prims.list;
  iquals: FStar_Syntax_Syntax.qualifier Prims.list;}
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
              let uu____434 = FStar_Syntax_Subst.open_term bs t in
              (match uu____434 with
               | (bs1,t1) ->
                   let datas1 =
                     FStar_All.pipe_right ses
                       (FStar_List.collect
                          (fun se1  ->
                             match se1.FStar_Syntax_Syntax.sigel with
                             | FStar_Syntax_Syntax.Sig_datacon
                                 (d,uu____447,t2,l',nparams,uu____451) when
                                 FStar_Ident.lid_equals l l' ->
                                 let uu____454 =
                                   FStar_Syntax_Util.arrow_formals t2 in
                                 (match uu____454 with
                                  | (bs',body) ->
                                      let uu____475 =
                                        FStar_Util.first_N
                                          (FStar_List.length bs1) bs' in
                                      (match uu____475 with
                                       | (bs_params,rest) ->
                                           let subst1 =
                                             FStar_List.map2
                                               (fun uu____511  ->
                                                  fun uu____512  ->
                                                    match (uu____511,
                                                            uu____512)
                                                    with
                                                    | ((b',uu____522),
                                                       (b,uu____524)) ->
                                                        let uu____529 =
                                                          let uu____534 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              b in
                                                          (b', uu____534) in
                                                        FStar_Syntax_Syntax.NT
                                                          uu____529)
                                               bs_params bs1 in
                                           let t3 =
                                             let uu____536 =
                                               let uu____539 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   body in
                                               FStar_Syntax_Util.arrow rest
                                                 uu____539 in
                                             FStar_All.pipe_right uu____536
                                               (FStar_Syntax_Subst.subst
                                                  subst1) in
                                           [{ dname = d; dtyp = t3 }]))
                             | uu____544 -> [])) in
                   [{
                      iname = l;
                      iparams = bs1;
                      ityp = t1;
                      idatas = datas1;
                      iquals = (se.FStar_Syntax_Syntax.sigquals)
                    }])
          | uu____545 -> []))
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
          let uu____586 =
            FStar_Extraction_ML_Term.term_as_mlty env1 ctor.dtyp in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env1) uu____586 in
        let steps =
          [FStar_TypeChecker_Normalize.Inlining;
          FStar_TypeChecker_Normalize.UnfoldUntil
            FStar_Syntax_Syntax.Delta_constant;
          FStar_TypeChecker_Normalize.EraseUniverses;
          FStar_TypeChecker_Normalize.AllowUnboundUniverses] in
        let names =
          let uu____591 =
            let uu____592 =
              let uu____595 =
                FStar_TypeChecker_Normalize.normalize steps
                  env1.FStar_Extraction_ML_UEnv.tcenv ctor.dtyp in
              FStar_Syntax_Subst.compress uu____595 in
            uu____592.FStar_Syntax_Syntax.n in
          match uu____591 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,uu____598) ->
              FStar_List.map
                (fun uu____611  ->
                   match uu____611 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____615;
                        FStar_Syntax_Syntax.sort = uu____616;_},uu____617)
                       -> ppname.FStar_Ident.idText) bs
          | uu____620 -> [] in
        let tys = (ml_tyvars, mlt) in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp in
        let uu____631 =
          let uu____632 =
            FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false in
          FStar_Pervasives_Native.fst uu____632 in
        let uu____635 =
          let uu____641 = lident_as_mlsymbol ctor.dname in
          let uu____642 =
            let uu____646 = FStar_Extraction_ML_Util.argTypes mlt in
            FStar_List.zip names uu____646 in
          (uu____641, uu____642) in
        (uu____631, uu____635) in
      let extract_one_family env1 ind =
        let uu____675 = binders_as_mlty_binders env1 ind.iparams in
        match uu____675 with
        | (env2,vars) ->
            let uu____701 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor vars) env2) in
            (match uu____701 with
             | (env3,ctors) ->
                 let uu____750 = FStar_Syntax_Util.arrow_formals ind.ityp in
                 (match uu____750 with
                  | (indices,uu____771) ->
                      let ml_params =
                        let uu____786 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____801  ->
                                    let uu____804 =
                                      let uu____805 =
                                        FStar_Util.string_of_int i in
                                      Prims.strcat "'dummyV" uu____805 in
                                    (uu____804, (Prims.parse_int "0")))) in
                        FStar_List.append vars uu____786 in
                      let tbody =
                        let uu____809 =
                          FStar_Util.find_opt
                            (fun uu___152_811  ->
                               match uu___152_811 with
                               | FStar_Syntax_Syntax.RecordType uu____812 ->
                                   true
                               | uu____817 -> false) ind.iquals in
                        match uu____809 with
                        | FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____824 = FStar_List.hd ctors in
                            (match uu____824 with
                             | (uu____835,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id  ->
                                        fun uu____853  ->
                                          match uu____853 with
                                          | (uu____858,ty) ->
                                              let lid =
                                                FStar_Ident.lid_of_ids
                                                  (FStar_List.append ns [id]) in
                                              let uu____861 =
                                                lident_as_mlsymbol lid in
                                              (uu____861, ty)) ids c_ty in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____862 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors in
                      let uu____864 =
                        let uu____875 = lident_as_mlsymbol ind.iname in
                        (false, uu____875, FStar_Pervasives_Native.None,
                          ml_params, (FStar_Pervasives_Native.Some tbody)) in
                      (env3, uu____864))) in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____896,t,uu____898,uu____899,uu____900);
            FStar_Syntax_Syntax.sigrng = uu____901;
            FStar_Syntax_Syntax.sigquals = uu____902;
            FStar_Syntax_Syntax.sigmeta = uu____903;_}::[],uu____904),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____912 = extract_ctor [] env { dname = l; dtyp = t } in
          (match uu____912 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____939),quals) ->
          let ifams = bundle_as_inductive_families env ses quals in
          let uu____950 = FStar_Util.fold_map extract_one_family env ifams in
          (match uu____950 with
           | (env1,td) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Ty td]))
      | uu____1002 -> failwith "Unexpected signature element"
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
           let uu____1023 = FStar_Syntax_Print.sigelt_to_string se in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____1023);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____1027 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____1032 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____1041 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
           ->
           let extend_env g1 lid ml_name tm tysc =
             let uu____1069 =
               let uu____1072 =
                 FStar_Syntax_Syntax.lid_as_fv lid
                   FStar_Syntax_Syntax.Delta_equational
                   FStar_Pervasives_Native.None in
               FStar_Extraction_ML_UEnv.extend_fv' g1 uu____1072 ml_name tysc
                 false false in
             match uu____1069 with
             | (g2,mangled_name) ->
                 ((let uu____1078 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          g2.FStar_Extraction_ML_UEnv.tcenv)
                       (FStar_Options.Other "ExtractionReify") in
                   if uu____1078
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
             (let uu____1090 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify") in
              if uu____1090
              then
                let uu____1091 = FStar_Syntax_Print.term_to_string tm in
                FStar_Util.print1 "extract_fv term: %s\n" uu____1091
              else ());
             (let uu____1093 =
                let uu____1094 = FStar_Syntax_Subst.compress tm in
                uu____1094.FStar_Syntax_Syntax.n in
              match uu____1093 with
              | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____1100) ->
                  extract_fv tm1
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let mlp =
                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  let uu____1111 =
                    let uu____1116 = FStar_Extraction_ML_UEnv.lookup_fv g fv in
                    FStar_All.pipe_left FStar_Util.right uu____1116 in
                  (match uu____1111 with
                   | (uu____1145,uu____1146,tysc,uu____1148) ->
                       let uu____1149 =
                         FStar_All.pipe_left
                           (FStar_Extraction_ML_Syntax.with_ty
                              FStar_Extraction_ML_Syntax.MLTY_Top)
                           (FStar_Extraction_ML_Syntax.MLE_Name mlp) in
                       (uu____1149, tysc))
              | uu____1150 -> failwith "Not an fv") in
           let extract_action g1 a =
             (let uu____1166 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g1.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify") in
              if uu____1166
              then
                let uu____1167 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_typ in
                let uu____1168 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_defn in
                FStar_Util.print2 "Action type %s and term %s\n" uu____1167
                  uu____1168
              else ());
             (let uu____1170 = FStar_Extraction_ML_UEnv.action_name ed a in
              match uu____1170 with
              | (a_nm,a_lid) ->
                  let lbname =
                    let uu____1180 =
                      FStar_Syntax_Syntax.new_bv
                        (FStar_Pervasives_Native.Some
                           ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                        FStar_Syntax_Syntax.tun in
                    FStar_Util.Inl uu____1180 in
                  let lb =
                    FStar_Syntax_Syntax.mk_lb
                      (lbname, (a.FStar_Syntax_Syntax.action_univs),
                        FStar_Parser_Const.effect_Tot_lid,
                        (a.FStar_Syntax_Syntax.action_typ),
                        (a.FStar_Syntax_Syntax.action_defn)) in
                  let lbs = (false, [lb]) in
                  let action_lb =
                    (FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_let
                          (lbs, FStar_Syntax_Util.exp_false_bool)))
                      FStar_Pervasives_Native.None
                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                  let uu____1205 =
                    FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb in
                  (match uu____1205 with
                   | (a_let,uu____1212,ty) ->
                       ((let uu____1215 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug
                                g1.FStar_Extraction_ML_UEnv.tcenv)
                             (FStar_Options.Other "ExtractionReify") in
                         if uu____1215
                         then
                           let uu____1216 =
                             FStar_Extraction_ML_Code.string_of_mlexpr a_nm
                               a_let in
                           FStar_Util.print1 "Extracted action term: %s\n"
                             uu____1216
                         else ());
                        (let uu____1218 =
                           match a_let.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_Let
                               ((uu____1223,uu____1224,mllb::[]),uu____1226)
                               ->
                               (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                                with
                                | FStar_Pervasives_Native.Some tysc ->
                                    ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                      tysc)
                                | FStar_Pervasives_Native.None  ->
                                    failwith "No type scheme")
                           | uu____1237 -> failwith "Impossible" in
                         match uu____1218 with
                         | (exp,tysc) ->
                             ((let uu____1245 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug
                                      g1.FStar_Extraction_ML_UEnv.tcenv)
                                   (FStar_Options.Other "ExtractionReify") in
                               if uu____1245
                               then
                                 ((let uu____1247 =
                                     FStar_Extraction_ML_Code.string_of_mlty
                                       a_nm
                                       (FStar_Pervasives_Native.snd tysc) in
                                   FStar_Util.print1
                                     "Extracted action type: %s\n" uu____1247);
                                  FStar_List.iter
                                    (fun x  ->
                                       FStar_Util.print1 "and binders: %s\n"
                                         (FStar_Pervasives_Native.fst x))
                                    (FStar_Pervasives_Native.fst tysc))
                               else ());
                              extend_env g1 a_lid a_nm exp tysc))))) in
           let uu____1254 =
             let uu____1257 =
               extract_fv
                 (FStar_Pervasives_Native.snd
                    ed.FStar_Syntax_Syntax.return_repr) in
             match uu____1257 with
             | (return_tm,ty_sc) ->
                 let uu____1265 =
                   FStar_Extraction_ML_UEnv.monad_op_name ed "return" in
                 (match uu____1265 with
                  | (return_nm,return_lid) ->
                      extend_env g return_lid return_nm return_tm ty_sc) in
           (match uu____1254 with
            | (g1,return_decl) ->
                let uu____1277 =
                  let uu____1280 =
                    extract_fv
                      (FStar_Pervasives_Native.snd
                         ed.FStar_Syntax_Syntax.bind_repr) in
                  match uu____1280 with
                  | (bind_tm,ty_sc) ->
                      let uu____1288 =
                        FStar_Extraction_ML_UEnv.monad_op_name ed "bind" in
                      (match uu____1288 with
                       | (bind_nm,bind_lid) ->
                           extend_env g1 bind_lid bind_nm bind_tm ty_sc) in
                (match uu____1277 with
                 | (g2,bind_decl) ->
                     let uu____1300 =
                       FStar_Util.fold_map extract_action g2
                         ed.FStar_Syntax_Syntax.actions in
                     (match uu____1300 with
                      | (g3,actions) ->
                          (g3,
                            (FStar_List.append [return_decl; bind_decl]
                               actions)))))
       | FStar_Syntax_Syntax.Sig_new_effect uu____1312 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____1315,t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____1319 =
             let uu____1320 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___153_1322  ->
                       match uu___153_1322 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____1323 -> false)) in
             Prims.op_Negation uu____1320 in
           if uu____1319
           then (g, [])
           else
             (let uu____1329 = FStar_Syntax_Util.arrow_formals t in
              match uu____1329 with
              | (bs,uu____1341) ->
                  let fv =
                    FStar_Syntax_Syntax.lid_as_fv lid
                      FStar_Syntax_Syntax.Delta_constant
                      FStar_Pervasives_Native.None in
                  let uu____1353 =
                    FStar_Syntax_Util.abs bs FStar_TypeChecker_Common.t_unit
                      FStar_Pervasives_Native.None in
                  extract_typ_abbrev g fv quals uu____1353)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____1360,uu____1361)
           when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____1372 =
             let uu____1377 =
               FStar_TypeChecker_Env.open_universes_in
                 g.FStar_Extraction_ML_UEnv.tcenv
                 lb.FStar_Syntax_Syntax.lbunivs
                 [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp] in
             match uu____1377 with
             | (tcenv,uu____1393,def_typ) ->
                 let uu____1397 = as_pair def_typ in (tcenv, uu____1397) in
           (match uu____1372 with
            | (tcenv,(lbdef,lbtyp)) ->
                let lbtyp1 =
                  FStar_TypeChecker_Normalize.unfold_whnf tcenv lbtyp in
                let lbdef1 =
                  FStar_TypeChecker_Normalize.eta_expand_with_type tcenv
                    lbdef lbtyp1 in
                let uu____1412 =
                  FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                extract_typ_abbrev g uu____1412 quals lbdef1)
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____1414,attrs) ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let elet =
             FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_let
                  (lbs, FStar_Syntax_Util.exp_false_bool))
               FStar_Pervasives_Native.None se.FStar_Syntax_Syntax.sigrng in
           let uu____1431 = FStar_Extraction_ML_Term.term_as_mlexpr g elet in
           (match uu____1431 with
            | (ml_let,uu____1439,uu____1440) ->
                (match ml_let.FStar_Extraction_ML_Syntax.expr with
                 | FStar_Extraction_ML_Syntax.MLE_Let
                     ((flavor,uu____1445,bindings),uu____1447) ->
                     let uu____1454 =
                       FStar_List.fold_left2
                         (fun uu____1461  ->
                            fun ml_lb  ->
                              fun uu____1463  ->
                                match (uu____1461, uu____1463) with
                                | ((env,ml_lbs),{
                                                  FStar_Syntax_Syntax.lbname
                                                    = lbname;
                                                  FStar_Syntax_Syntax.lbunivs
                                                    = uu____1476;
                                                  FStar_Syntax_Syntax.lbtyp =
                                                    t;
                                                  FStar_Syntax_Syntax.lbeff =
                                                    uu____1478;
                                                  FStar_Syntax_Syntax.lbdef =
                                                    uu____1479;_})
                                    ->
                                    let lb_lid =
                                      let uu____1493 =
                                        let uu____1498 =
                                          FStar_Util.right lbname in
                                        uu____1498.FStar_Syntax_Syntax.fv_name in
                                      uu____1493.FStar_Syntax_Syntax.v in
                                    let uu____1502 =
                                      let uu____1505 =
                                        FStar_All.pipe_right quals
                                          (FStar_Util.for_some
                                             (fun uu___154_1507  ->
                                                match uu___154_1507 with
                                                | FStar_Syntax_Syntax.Projector
                                                    uu____1508 -> true
                                                | uu____1511 -> false)) in
                                      if uu____1505
                                      then
                                        let mname =
                                          let uu____1515 =
                                            mangle_projector_lid lb_lid in
                                          FStar_All.pipe_right uu____1515
                                            FStar_Extraction_ML_Syntax.mlpath_of_lident in
                                        let uu____1516 =
                                          let uu____1519 =
                                            FStar_Util.right lbname in
                                          let uu____1520 =
                                            FStar_Util.must
                                              ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc in
                                          FStar_Extraction_ML_UEnv.extend_fv'
                                            env uu____1519 mname uu____1520
                                            ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                            false in
                                        match uu____1516 with
                                        | (env1,uu____1524) ->
                                            (env1,
                                              (let uu___160_1525 = ml_lb in
                                               {
                                                 FStar_Extraction_ML_Syntax.mllb_name
                                                   =
                                                   ((FStar_Pervasives_Native.snd
                                                       mname),
                                                     (Prims.parse_int "0"));
                                                 FStar_Extraction_ML_Syntax.mllb_tysc
                                                   =
                                                   (uu___160_1525.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                 FStar_Extraction_ML_Syntax.mllb_add_unit
                                                   =
                                                   (uu___160_1525.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                 FStar_Extraction_ML_Syntax.mllb_def
                                                   =
                                                   (uu___160_1525.FStar_Extraction_ML_Syntax.mllb_def);
                                                 FStar_Extraction_ML_Syntax.print_typ
                                                   =
                                                   (uu___160_1525.FStar_Extraction_ML_Syntax.print_typ)
                                               }))
                                      else
                                        (let uu____1528 =
                                           let uu____1529 =
                                             let uu____1532 =
                                               FStar_Util.must
                                                 ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc in
                                             FStar_Extraction_ML_UEnv.extend_lb
                                               env lbname t uu____1532
                                               ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                               false in
                                           FStar_All.pipe_left
                                             FStar_Pervasives_Native.fst
                                             uu____1529 in
                                         (uu____1528, ml_lb)) in
                                    (match uu____1502 with
                                     | (g1,ml_lb1) ->
                                         (g1, (ml_lb1 :: ml_lbs)))) (g, [])
                         bindings (FStar_Pervasives_Native.snd lbs) in
                     (match uu____1454 with
                      | (g1,ml_lbs') ->
                          let has_noextract =
                            FStar_List.existsb
                              (fun uu___155_1551  ->
                                 match uu___155_1551 with
                                 | FStar_Syntax_Syntax.NoExtract  -> true
                                 | uu____1552 -> false) quals in
                          let flags =
                            FStar_List.choose
                              (fun uu___156_1555  ->
                                 match uu___156_1555 with
                                 | FStar_Syntax_Syntax.Assumption  ->
                                     FStar_Pervasives_Native.Some
                                       FStar_Extraction_ML_Syntax.Assumed
                                 | FStar_Syntax_Syntax.Private  ->
                                     FStar_Pervasives_Native.Some
                                       FStar_Extraction_ML_Syntax.Private
                                 | FStar_Syntax_Syntax.NoExtract  ->
                                     FStar_Pervasives_Native.Some
                                       FStar_Extraction_ML_Syntax.NoExtract
                                 | uu____1557 -> FStar_Pervasives_Native.None)
                              quals in
                          let flags' =
                            FStar_List.choose
                              (fun uu___157_1562  ->
                                 match uu___157_1562 with
                                 | {
                                     FStar_Syntax_Syntax.n =
                                       FStar_Syntax_Syntax.Tm_constant
                                       (FStar_Const.Const_string
                                       (data,uu____1567));
                                     FStar_Syntax_Syntax.tk = uu____1568;
                                     FStar_Syntax_Syntax.pos = uu____1569;
                                     FStar_Syntax_Syntax.vars = uu____1570;_}
                                     ->
                                     FStar_Pervasives_Native.Some
                                       (FStar_Extraction_ML_Syntax.Attribute
                                          (FStar_Util.string_of_unicode data))
                                 | uu____1575 ->
                                     (FStar_Util.print_warning
                                        "Warning: unrecognized, non-string attribute, bother protz for a better error message";
                                      FStar_Pervasives_Native.None)) attrs in
                          let uu____1579 =
                            let uu____1581 =
                              has_noextract &&
                                (let uu____1582 = is_kremlin () in
                                 Prims.op_Negation uu____1582) in
                            if uu____1581
                            then []
                            else
                              (let uu____1585 =
                                 let uu____1586 =
                                   FStar_Extraction_ML_Util.mlloc_of_range
                                     se.FStar_Syntax_Syntax.sigrng in
                                 FStar_Extraction_ML_Syntax.MLM_Loc
                                   uu____1586 in
                               [uu____1585;
                               FStar_Extraction_ML_Syntax.MLM_Let
                                 (flavor, (FStar_List.append flags flags'),
                                   (FStar_List.rev ml_lbs'))]) in
                          (g1, uu____1579))
                 | uu____1590 ->
                     let uu____1591 =
                       let uu____1592 =
                         FStar_Extraction_ML_Code.string_of_mlexpr
                           g.FStar_Extraction_ML_UEnv.currentModule ml_let in
                       FStar_Util.format1
                         "Impossible: Translated a let to a non-let: %s"
                         uu____1592 in
                     failwith uu____1591))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____1597,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____1601 =
             FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption) in
           if uu____1601
           then
             let always_fail =
               let imp =
                 let uu____1608 = FStar_Syntax_Util.arrow_formals t in
                 match uu____1608 with
                 | ([],t1) ->
                     let b =
                       let uu____1627 =
                         FStar_Syntax_Syntax.gen_bv "_"
                           FStar_Pervasives_Native.None t1 in
                       FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                         uu____1627 in
                     let uu____1628 = fail_exp lid t1 in
                     FStar_Syntax_Util.abs [b] uu____1628
                       FStar_Pervasives_Native.None
                 | (bs,t1) ->
                     let uu____1646 = fail_exp lid t1 in
                     FStar_Syntax_Util.abs bs uu____1646
                       FStar_Pervasives_Native.None in
               let uu___161_1652 = se in
               let uu____1653 =
                 let uu____1654 =
                   let uu____1660 =
                     let uu____1664 =
                       let uu____1666 =
                         let uu____1667 =
                           let uu____1670 =
                             FStar_Syntax_Syntax.lid_as_fv lid
                               FStar_Syntax_Syntax.Delta_constant
                               FStar_Pervasives_Native.None in
                           FStar_Util.Inr uu____1670 in
                         {
                           FStar_Syntax_Syntax.lbname = uu____1667;
                           FStar_Syntax_Syntax.lbunivs = [];
                           FStar_Syntax_Syntax.lbtyp = t;
                           FStar_Syntax_Syntax.lbeff =
                             FStar_Parser_Const.effect_ML_lid;
                           FStar_Syntax_Syntax.lbdef = imp
                         } in
                       [uu____1666] in
                     (false, uu____1664) in
                   (uu____1660, [], []) in
                 FStar_Syntax_Syntax.Sig_let uu____1654 in
               {
                 FStar_Syntax_Syntax.sigel = uu____1653;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___161_1652.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___161_1652.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___161_1652.FStar_Syntax_Syntax.sigmeta)
               } in
             let uu____1677 = extract_sig g always_fail in
             (match uu____1677 with
              | (g1,mlm) ->
                  let uu____1688 =
                    FStar_Util.find_map quals
                      (fun uu___158_1690  ->
                         match uu___158_1690 with
                         | FStar_Syntax_Syntax.Discriminator l ->
                             FStar_Pervasives_Native.Some l
                         | uu____1693 -> FStar_Pervasives_Native.None) in
                  (match uu____1688 with
                   | FStar_Pervasives_Native.Some l ->
                       let uu____1698 =
                         let uu____1700 =
                           let uu____1701 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____1701 in
                         let uu____1702 =
                           let uu____1704 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l in
                           [uu____1704] in
                         uu____1700 :: uu____1702 in
                       (g1, uu____1698)
                   | uu____1706 ->
                       let uu____1708 =
                         FStar_Util.find_map quals
                           (fun uu___159_1710  ->
                              match uu___159_1710 with
                              | FStar_Syntax_Syntax.Projector (l,uu____1713)
                                  -> FStar_Pervasives_Native.Some l
                              | uu____1714 -> FStar_Pervasives_Native.None) in
                       (match uu____1708 with
                        | FStar_Pervasives_Native.Some uu____1718 -> (g1, [])
                        | uu____1720 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____1726 = FStar_Extraction_ML_Term.term_as_mlexpr g e in
           (match uu____1726 with
            | (ml_main,uu____1734,uu____1735) ->
                let uu____1736 =
                  let uu____1738 =
                    let uu____1739 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____1739 in
                  [uu____1738; FStar_Extraction_ML_Syntax.MLM_Top ml_main] in
                (g, uu____1736))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____1741 ->
           failwith "impossible -- removed by tc.fs"
       | FStar_Syntax_Syntax.Sig_assume uu____1745 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____1749 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____1751 -> (g, [])
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (if p = FStar_Syntax_Syntax.LightOff
            then FStar_Options.set_ml_ish ()
            else ();
            (g, [])))
let extract_iface:
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.modul -> env_t =
  fun g  ->
    fun m  ->
      let uu____1769 =
        FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____1769 FStar_Pervasives_Native.fst
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
      (let uu____1795 = FStar_Options.debug_any () in
       if uu____1795
       then
         let uu____1796 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
         FStar_Util.print1 "Extracting module %s\n" uu____1796
       else ());
      (let uu____1798 = FStar_Options.restore_cmd_line_options true in
       let name =
         FStar_Extraction_ML_Syntax.mlpath_of_lident
           m.FStar_Syntax_Syntax.name in
       let g1 =
         let uu___162_1801 = g in
         {
           FStar_Extraction_ML_UEnv.tcenv =
             (uu___162_1801.FStar_Extraction_ML_UEnv.tcenv);
           FStar_Extraction_ML_UEnv.gamma =
             (uu___162_1801.FStar_Extraction_ML_UEnv.gamma);
           FStar_Extraction_ML_UEnv.tydefs =
             (uu___162_1801.FStar_Extraction_ML_UEnv.tydefs);
           FStar_Extraction_ML_UEnv.currentModule = name
         } in
       let uu____1802 =
         FStar_Util.fold_map extract_sig g1
           m.FStar_Syntax_Syntax.declarations in
       match uu____1802 with
       | (g2,sigs) ->
           let mlm = FStar_List.flatten sigs in
           let uu____1818 =
             (((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
                ((is_kremlin ()) ||
                   (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)))
               &&
               (FStar_Options.should_extract
                  (m.FStar_Syntax_Syntax.name).FStar_Ident.str) in
           if uu____1818
           then
             ((let uu____1823 =
                 FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
               FStar_Util.print1 "Extracted module %s\n" uu____1823);
              (g2,
                [FStar_Extraction_ML_Syntax.MLLib
                   [(name, (FStar_Pervasives_Native.Some ([], mlm)),
                      (FStar_Extraction_ML_Syntax.MLLib []))]]))
           else (g2, []))