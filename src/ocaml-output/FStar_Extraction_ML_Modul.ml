open Prims
let fail_exp lid t =
  let uu____17 =
    let uu____22 =
      let uu____23 =
        let uu____42 =
          FStar_Syntax_Syntax.fvar FStar_Parser_Const.failwith_lid
            FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None in
        let uu____43 =
          let uu____46 = FStar_Syntax_Syntax.iarg t in
          let uu____47 =
            let uu____50 =
              let uu____51 =
                let uu____52 =
                  let uu____57 =
                    let uu____58 =
                      let uu____59 =
                        let uu____66 =
                          let uu____67 =
                            let uu____68 =
                              FStar_Syntax_Print.lid_to_string lid in
                            Prims.strcat "Not yet implemented:" uu____68 in
                          FStar_Bytes.string_as_unicode_bytes uu____67 in
                        (uu____66, FStar_Range.dummyRange) in
                      FStar_Const.Const_string uu____59 in
                    FStar_Syntax_Syntax.Tm_constant uu____58 in
                  FStar_Syntax_Syntax.mk uu____57 in
                uu____52 FStar_Pervasives_Native.None FStar_Range.dummyRange in
              FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____51 in
            [uu____50] in
          uu____46 :: uu____47 in
        (uu____42, uu____43) in
      FStar_Syntax_Syntax.Tm_app uu____23 in
    FStar_Syntax_Syntax.mk uu____22 in
  uu____17 FStar_Pervasives_Native.None FStar_Range.dummyRange
let mangle_projector_lid: FStar_Ident.lident -> FStar_Ident.lident =
  fun x  -> x
let lident_as_mlsymbol: FStar_Ident.lident -> Prims.string =
  fun id  -> (id.FStar_Ident.ident).FStar_Ident.idText
let as_pair uu___148_97 =
  match uu___148_97 with
  | a::b::[] -> (a, b)
  | uu____102 -> failwith "Expected a list with 2 elements"
let binders_as_mlty_binders env bs =
  FStar_Util.fold_map
    (fun env1  ->
       fun uu____152  ->
         match uu____152 with
         | (bv,uu____166) ->
             let uu____167 =
               let uu____168 =
                 let uu____171 =
                   let uu____172 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv in
                   FStar_Extraction_ML_Syntax.MLTY_Var uu____172 in
                 FStar_Pervasives_Native.Some uu____171 in
               FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____168 in
             let uu____173 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv in
             (uu____167, uu____173)) env bs
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
            let uu____210 =
              let uu____211 = FStar_Syntax_Subst.compress def in
              FStar_All.pipe_right uu____211 FStar_Syntax_Util.unmeta in
            FStar_All.pipe_right uu____210 FStar_Syntax_Util.un_uinst in
          let def2 =
            match def1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs uu____213 ->
                FStar_Extraction_ML_Term.normalize_abs def1
            | uu____242 -> def1 in
          let uu____243 =
            match def2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____254) ->
                FStar_Syntax_Subst.open_term bs body
            | uu____299 -> ([], def2) in
          match uu____243 with
          | (bs,body) ->
              let assumed =
                FStar_Util.for_some
                  (fun uu___149_319  ->
                     match uu___149_319 with
                     | FStar_Syntax_Syntax.Assumption  -> true
                     | uu____320 -> false) quals in
              let uu____321 = binders_as_mlty_binders env bs in
              (match uu____321 with
               | (env1,ml_bs) ->
                   let body1 =
                     let uu____353 =
                       FStar_Extraction_ML_Term.term_as_mlty env1 body in
                     FStar_All.pipe_right uu____353
                       (FStar_Extraction_ML_Util.eraseTypeDeep
                          (FStar_Extraction_ML_Util.udelta_unfold env1)) in
                   let mangled_projector =
                     let uu____357 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___150_360  ->
                               match uu___150_360 with
                               | FStar_Syntax_Syntax.Projector uu____361 ->
                                   true
                               | uu____366 -> false)) in
                     if uu____357
                     then
                       let mname = mangle_projector_lid lid in
                       FStar_Pervasives_Native.Some
                         ((mname.FStar_Ident.ident).FStar_Ident.idText)
                     else FStar_Pervasives_Native.None in
                   let td =
                     let uu____394 =
                       let uu____415 = lident_as_mlsymbol lid in
                       (assumed, uu____415, mangled_projector, ml_bs,
                         (FStar_Pervasives_Native.Some
                            (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1))) in
                     [uu____394] in
                   let def3 =
                     let uu____469 =
                       let uu____470 =
                         FStar_Extraction_ML_Util.mlloc_of_range
                           (FStar_Ident.range_of_lid lid) in
                       FStar_Extraction_ML_Syntax.MLM_Loc uu____470 in
                     [uu____469; FStar_Extraction_ML_Syntax.MLM_Ty td] in
                   let env2 =
                     let uu____472 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___151_475  ->
                               match uu___151_475 with
                               | FStar_Syntax_Syntax.Assumption  -> true
                               | FStar_Syntax_Syntax.New  -> true
                               | uu____476 -> false)) in
                     if uu____472
                     then FStar_Extraction_ML_UEnv.extend_type_name env1 fv
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
    let uu____551 = FStar_Syntax_Print.lid_to_string i.iname in
    let uu____552 = FStar_Syntax_Print.binders_to_string " " i.iparams in
    let uu____553 = FStar_Syntax_Print.term_to_string i.ityp in
    let uu____554 =
      let uu____555 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let uu____563 = FStar_Syntax_Print.lid_to_string d.dname in
                let uu____564 =
                  let uu____565 = FStar_Syntax_Print.term_to_string d.dtyp in
                  Prims.strcat " : " uu____565 in
                Prims.strcat uu____563 uu____564)) in
      FStar_All.pipe_right uu____555 (FStar_String.concat "\n\t\t") in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____551 uu____552 uu____553
      uu____554
let bundle_as_inductive_families env ses quals =
  let uu____595 =
    FStar_Util.fold_map
      (fun env1  ->
         fun se  ->
           match se.FStar_Syntax_Syntax.sigel with
           | FStar_Syntax_Syntax.Sig_inductive_typ (l,_us,bs,t,_mut_i,datas)
               ->
               let uu____628 = FStar_Syntax_Subst.open_term bs t in
               (match uu____628 with
                | (bs1,t1) ->
                    let datas1 =
                      FStar_All.pipe_right ses
                        (FStar_List.collect
                           (fun se1  ->
                              match se1.FStar_Syntax_Syntax.sigel with
                              | FStar_Syntax_Syntax.Sig_datacon
                                  (d,uu____652,t2,l',nparams,uu____656) when
                                  FStar_Ident.lid_equals l l' ->
                                  let uu____661 =
                                    FStar_Syntax_Util.arrow_formals t2 in
                                  (match uu____661 with
                                   | (bs',body) ->
                                       let uu____700 =
                                         FStar_Util.first_N
                                           (FStar_List.length bs1) bs' in
                                       (match uu____700 with
                                        | (bs_params,rest) ->
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____764  ->
                                                   fun uu____765  ->
                                                     match (uu____764,
                                                             uu____765)
                                                     with
                                                     | ((b',uu____783),
                                                        (b,uu____785)) ->
                                                         let uu____794 =
                                                           let uu____803 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (b', uu____803) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____794)
                                                bs_params bs1 in
                                            let t3 =
                                              let uu____805 =
                                                let uu____810 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    body in
                                                FStar_Syntax_Util.arrow rest
                                                  uu____810 in
                                              FStar_All.pipe_right uu____805
                                                (FStar_Syntax_Subst.subst
                                                   subst1) in
                                            [{ dname = d; dtyp = t3 }]))
                              | uu____819 -> [])) in
                    let env2 =
                      let uu____821 =
                        FStar_Syntax_Syntax.lid_as_fv l
                          FStar_Syntax_Syntax.Delta_constant
                          FStar_Pervasives_Native.None in
                      FStar_Extraction_ML_UEnv.extend_type_name env1
                        uu____821 in
                    (env2,
                      [{
                         iname = l;
                         iparams = bs1;
                         ityp = t1;
                         idatas = datas1;
                         iquals = (se.FStar_Syntax_Syntax.sigquals)
                       }]))
           | uu____824 -> (env1, [])) env ses in
  match uu____595 with | (env1,ifams) -> (env1, (FStar_List.flatten ifams))
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
          let uu____908 =
            FStar_Extraction_ML_Term.term_as_mlty env1 ctor.dtyp in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env1) uu____908 in
        let steps =
          [FStar_TypeChecker_Normalize.Inlining;
          FStar_TypeChecker_Normalize.UnfoldUntil
            FStar_Syntax_Syntax.Delta_constant;
          FStar_TypeChecker_Normalize.EraseUniverses;
          FStar_TypeChecker_Normalize.AllowUnboundUniverses] in
        let names =
          let uu____915 =
            let uu____916 =
              let uu____921 =
                FStar_TypeChecker_Normalize.normalize steps
                  env1.FStar_Extraction_ML_UEnv.tcenv ctor.dtyp in
              FStar_Syntax_Subst.compress uu____921 in
            uu____916.FStar_Syntax_Syntax.n in
          match uu____915 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,uu____925) ->
              FStar_List.map
                (fun uu____950  ->
                   match uu____950 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____956;
                        FStar_Syntax_Syntax.sort = uu____957;_},uu____958)
                       -> ppname.FStar_Ident.idText) bs
          | uu____963 -> [] in
        let tys = (ml_tyvars, mlt) in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp in
        let uu____982 =
          let uu____983 =
            FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false in
          FStar_Pervasives_Native.fst uu____983 in
        let uu____988 =
          let uu____999 = lident_as_mlsymbol ctor.dname in
          let uu____1000 =
            let uu____1007 = FStar_Extraction_ML_Util.argTypes mlt in
            FStar_List.zip names uu____1007 in
          (uu____999, uu____1000) in
        (uu____982, uu____988) in
      let extract_one_family env1 ind =
        let uu____1057 = binders_as_mlty_binders env1 ind.iparams in
        match uu____1057 with
        | (env2,vars) ->
            let uu____1106 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor vars) env2) in
            (match uu____1106 with
             | (env3,ctors) ->
                 let uu____1201 = FStar_Syntax_Util.arrow_formals ind.ityp in
                 (match uu____1201 with
                  | (indices,uu____1241) ->
                      let ml_params =
                        let uu____1269 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____1297  ->
                                    let uu____1302 =
                                      let uu____1303 =
                                        FStar_Util.string_of_int i in
                                      Prims.strcat "'dummyV" uu____1303 in
                                    (uu____1302, (Prims.parse_int "0")))) in
                        FStar_List.append vars uu____1269 in
                      let tbody =
                        let uu____1309 =
                          FStar_Util.find_opt
                            (fun uu___152_1312  ->
                               match uu___152_1312 with
                               | FStar_Syntax_Syntax.RecordType uu____1313 ->
                                   true
                               | uu____1322 -> false) ind.iquals in
                        match uu____1309 with
                        | FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____1333 = FStar_List.hd ctors in
                            (match uu____1333 with
                             | (uu____1354,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id  ->
                                        fun uu____1387  ->
                                          match uu____1387 with
                                          | (uu____1396,ty) ->
                                              let lid =
                                                FStar_Ident.lid_of_ids
                                                  (FStar_List.append ns [id]) in
                                              let uu____1399 =
                                                lident_as_mlsymbol lid in
                                              (uu____1399, ty)) ids c_ty in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____1400 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors in
                      let uu____1403 =
                        let uu____1424 = lident_as_mlsymbol ind.iname in
                        (false, uu____1424, FStar_Pervasives_Native.None,
                          ml_params, (FStar_Pervasives_Native.Some tbody)) in
                      (env3, uu____1403))) in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____1464,t,uu____1466,uu____1467,uu____1468);
            FStar_Syntax_Syntax.sigrng = uu____1469;
            FStar_Syntax_Syntax.sigquals = uu____1470;
            FStar_Syntax_Syntax.sigmeta = uu____1471;_}::[],uu____1472),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____1487 = extract_ctor [] env { dname = l; dtyp = t } in
          (match uu____1487 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____1537),quals) ->
          let uu____1551 = bundle_as_inductive_families env ses quals in
          (match uu____1551 with
           | (env1,ifams) ->
               let uu____1572 =
                 FStar_Util.fold_map extract_one_family env1 ifams in
               (match uu____1572 with
                | (env2,td) -> (env2, [FStar_Extraction_ML_Syntax.MLM_Ty td])))
      | uu____1673 -> failwith "Unexpected signature element"
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
           let uu____1706 = FStar_Syntax_Print.sigelt_to_string se in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____1706);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____1713 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____1722 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____1739 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
           ->
           let extend_env g1 lid ml_name tm tysc =
             let uu____1777 =
               let uu____1782 =
                 FStar_Syntax_Syntax.lid_as_fv lid
                   FStar_Syntax_Syntax.Delta_equational
                   FStar_Pervasives_Native.None in
               FStar_Extraction_ML_UEnv.extend_fv' g1 uu____1782 ml_name tysc
                 false false in
             match uu____1777 with
             | (g2,mangled_name) ->
                 ((let uu____1790 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          g2.FStar_Extraction_ML_UEnv.tcenv)
                       (FStar_Options.Other "ExtractionReify") in
                   if uu____1790
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
             (let uu____1806 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify") in
              if uu____1806
              then
                let uu____1807 = FStar_Syntax_Print.term_to_string tm in
                FStar_Util.print1 "extract_fv term: %s\n" uu____1807
              else ());
             (let uu____1809 =
                let uu____1810 = FStar_Syntax_Subst.compress tm in
                uu____1810.FStar_Syntax_Syntax.n in
              match uu____1809 with
              | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____1820) ->
                  extract_fv tm1
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let mlp =
                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  let uu____1835 =
                    let uu____1844 = FStar_Extraction_ML_UEnv.lookup_fv g fv in
                    FStar_All.pipe_left FStar_Util.right uu____1844 in
                  (match uu____1835 with
                   | (uu____1901,uu____1902,tysc,uu____1904) ->
                       let uu____1905 =
                         FStar_All.pipe_left
                           (FStar_Extraction_ML_Syntax.with_ty
                              FStar_Extraction_ML_Syntax.MLTY_Top)
                           (FStar_Extraction_ML_Syntax.MLE_Name mlp) in
                       (uu____1905, tysc))
              | uu____1906 -> failwith "Not an fv") in
           let extract_action g1 a =
             (let uu____1926 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g1.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify") in
              if uu____1926
              then
                let uu____1927 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_typ in
                let uu____1928 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_defn in
                FStar_Util.print2 "Action type %s and term %s\n" uu____1927
                  uu____1928
              else ());
             (let uu____1930 = FStar_Extraction_ML_UEnv.action_name ed a in
              match uu____1930 with
              | (a_nm,a_lid) ->
                  let lbname =
                    let uu____1946 =
                      FStar_Syntax_Syntax.new_bv
                        (FStar_Pervasives_Native.Some
                           ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                        FStar_Syntax_Syntax.tun in
                    FStar_Util.Inl uu____1946 in
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
                  let uu____1976 =
                    FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb in
                  (match uu____1976 with
                   | (a_let,uu____1988,ty) ->
                       ((let uu____1991 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug
                                g1.FStar_Extraction_ML_UEnv.tcenv)
                             (FStar_Options.Other "ExtractionReify") in
                         if uu____1991
                         then
                           let uu____1992 =
                             FStar_Extraction_ML_Code.string_of_mlexpr a_nm
                               a_let in
                           FStar_Util.print1 "Extracted action term: %s\n"
                             uu____1992
                         else ());
                        (let uu____1994 =
                           match a_let.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_Let
                               ((uu____2003,uu____2004,mllb::[]),uu____2006)
                               ->
                               (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                                with
                                | FStar_Pervasives_Native.Some tysc ->
                                    ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                      tysc)
                                | FStar_Pervasives_Native.None  ->
                                    failwith "No type scheme")
                           | uu____2026 -> failwith "Impossible" in
                         match uu____1994 with
                         | (exp,tysc) ->
                             ((let uu____2038 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug
                                      g1.FStar_Extraction_ML_UEnv.tcenv)
                                   (FStar_Options.Other "ExtractionReify") in
                               if uu____2038
                               then
                                 ((let uu____2040 =
                                     FStar_Extraction_ML_Code.string_of_mlty
                                       a_nm
                                       (FStar_Pervasives_Native.snd tysc) in
                                   FStar_Util.print1
                                     "Extracted action type: %s\n" uu____2040);
                                  FStar_List.iter
                                    (fun x  ->
                                       FStar_Util.print1 "and binders: %s\n"
                                         (FStar_Pervasives_Native.fst x))
                                    (FStar_Pervasives_Native.fst tysc))
                               else ());
                              extend_env g1 a_lid a_nm exp tysc))))) in
           let uu____2051 =
             let uu____2056 =
               extract_fv
                 (FStar_Pervasives_Native.snd
                    ed.FStar_Syntax_Syntax.return_repr) in
             match uu____2056 with
             | (return_tm,ty_sc) ->
                 let uu____2069 =
                   FStar_Extraction_ML_UEnv.monad_op_name ed "return" in
                 (match uu____2069 with
                  | (return_nm,return_lid) ->
                      extend_env g return_lid return_nm return_tm ty_sc) in
           (match uu____2051 with
            | (g1,return_decl) ->
                let uu____2088 =
                  let uu____2093 =
                    extract_fv
                      (FStar_Pervasives_Native.snd
                         ed.FStar_Syntax_Syntax.bind_repr) in
                  match uu____2093 with
                  | (bind_tm,ty_sc) ->
                      let uu____2106 =
                        FStar_Extraction_ML_UEnv.monad_op_name ed "bind" in
                      (match uu____2106 with
                       | (bind_nm,bind_lid) ->
                           extend_env g1 bind_lid bind_nm bind_tm ty_sc) in
                (match uu____2088 with
                 | (g2,bind_decl) ->
                     let uu____2125 =
                       FStar_Util.fold_map extract_action g2
                         ed.FStar_Syntax_Syntax.actions in
                     (match uu____2125 with
                      | (g3,actions) ->
                          (g3,
                            (FStar_List.append [return_decl; bind_decl]
                               actions)))))
       | FStar_Syntax_Syntax.Sig_new_effect uu____2146 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____2150,t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____2155 =
             let uu____2156 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___153_2159  ->
                       match uu___153_2159 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____2160 -> false)) in
             Prims.op_Negation uu____2156 in
           if uu____2155
           then (g, [])
           else
             (let uu____2170 = FStar_Syntax_Util.arrow_formals t in
              match uu____2170 with
              | (bs,uu____2192) ->
                  let fv =
                    FStar_Syntax_Syntax.lid_as_fv lid
                      FStar_Syntax_Syntax.Delta_constant
                      FStar_Pervasives_Native.None in
                  let uu____2214 =
                    FStar_Syntax_Util.abs bs FStar_TypeChecker_Common.t_unit
                      FStar_Pervasives_Native.None in
                  extract_typ_abbrev g fv quals uu____2214)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____2226,uu____2227)
           when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____2247 =
             let uu____2256 =
               FStar_TypeChecker_Env.open_universes_in
                 g.FStar_Extraction_ML_UEnv.tcenv
                 lb.FStar_Syntax_Syntax.lbunivs
                 [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp] in
             match uu____2256 with
             | (tcenv,uu____2286,def_typ) ->
                 let uu____2292 = as_pair def_typ in (tcenv, uu____2292) in
           (match uu____2247 with
            | (tcenv,(lbdef,lbtyp)) ->
                let lbtyp1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.UnfoldUntil
                      FStar_Syntax_Syntax.Delta_constant] tcenv lbtyp in
                let lbdef1 =
                  FStar_TypeChecker_Normalize.eta_expand_with_type tcenv
                    lbdef lbtyp1 in
                let uu____2316 =
                  FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                extract_typ_abbrev g uu____2316 quals lbdef1)
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____2318,attrs) ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let elet =
             FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_let
                  (lbs, FStar_Syntax_Util.exp_false_bool))
               FStar_Pervasives_Native.None se.FStar_Syntax_Syntax.sigrng in
           let uu____2340 = FStar_Extraction_ML_Term.term_as_mlexpr g elet in
           (match uu____2340 with
            | (ml_let,uu____2354,uu____2355) ->
                (match ml_let.FStar_Extraction_ML_Syntax.expr with
                 | FStar_Extraction_ML_Syntax.MLE_Let
                     ((flavor,uu____2363,bindings),uu____2365) ->
                     let uu____2378 =
                       FStar_List.fold_left2
                         (fun uu____2391  ->
                            fun ml_lb  ->
                              fun uu____2393  ->
                                match (uu____2391, uu____2393) with
                                | ((env,ml_lbs),{
                                                  FStar_Syntax_Syntax.lbname
                                                    = lbname;
                                                  FStar_Syntax_Syntax.lbunivs
                                                    = uu____2415;
                                                  FStar_Syntax_Syntax.lbtyp =
                                                    t;
                                                  FStar_Syntax_Syntax.lbeff =
                                                    uu____2417;
                                                  FStar_Syntax_Syntax.lbdef =
                                                    uu____2418;_})
                                    ->
                                    let lb_lid =
                                      let uu____2444 =
                                        let uu____2453 =
                                          FStar_Util.right lbname in
                                        uu____2453.FStar_Syntax_Syntax.fv_name in
                                      uu____2444.FStar_Syntax_Syntax.v in
                                    let uu____2458 =
                                      let uu____2463 =
                                        FStar_All.pipe_right quals
                                          (FStar_Util.for_some
                                             (fun uu___154_2466  ->
                                                match uu___154_2466 with
                                                | FStar_Syntax_Syntax.Projector
                                                    uu____2467 -> true
                                                | uu____2472 -> false)) in
                                      if uu____2463
                                      then
                                        let mname =
                                          let uu____2478 =
                                            mangle_projector_lid lb_lid in
                                          FStar_All.pipe_right uu____2478
                                            FStar_Extraction_ML_Syntax.mlpath_of_lident in
                                        let uu____2479 =
                                          let uu____2484 =
                                            FStar_Util.right lbname in
                                          let uu____2485 =
                                            FStar_Util.must
                                              ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc in
                                          FStar_Extraction_ML_UEnv.extend_fv'
                                            env uu____2484 mname uu____2485
                                            ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                            false in
                                        match uu____2479 with
                                        | (env1,uu____2491) ->
                                            (env1,
                                              (let uu___159_2492 = ml_lb in
                                               {
                                                 FStar_Extraction_ML_Syntax.mllb_name
                                                   =
                                                   ((FStar_Pervasives_Native.snd
                                                       mname),
                                                     (Prims.parse_int "0"));
                                                 FStar_Extraction_ML_Syntax.mllb_tysc
                                                   =
                                                   (uu___159_2492.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                 FStar_Extraction_ML_Syntax.mllb_add_unit
                                                   =
                                                   (uu___159_2492.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                 FStar_Extraction_ML_Syntax.mllb_def
                                                   =
                                                   (uu___159_2492.FStar_Extraction_ML_Syntax.mllb_def);
                                                 FStar_Extraction_ML_Syntax.print_typ
                                                   =
                                                   (uu___159_2492.FStar_Extraction_ML_Syntax.print_typ)
                                               }))
                                      else
                                        (let uu____2496 =
                                           let uu____2497 =
                                             let uu____2502 =
                                               FStar_Util.must
                                                 ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc in
                                             FStar_Extraction_ML_UEnv.extend_lb
                                               env lbname t uu____2502
                                               ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                               false in
                                           FStar_All.pipe_left
                                             FStar_Pervasives_Native.fst
                                             uu____2497 in
                                         (uu____2496, ml_lb)) in
                                    (match uu____2458 with
                                     | (g1,ml_lb1) ->
                                         (g1, (ml_lb1 :: ml_lbs)))) (g, [])
                         bindings (FStar_Pervasives_Native.snd lbs) in
                     (match uu____2378 with
                      | (g1,ml_lbs') ->
                          let flags =
                            FStar_List.choose
                              (fun uu___155_2536  ->
                                 match uu___155_2536 with
                                 | FStar_Syntax_Syntax.Assumption  ->
                                     FStar_Pervasives_Native.Some
                                       FStar_Extraction_ML_Syntax.Assumed
                                 | FStar_Syntax_Syntax.Private  ->
                                     FStar_Pervasives_Native.Some
                                       FStar_Extraction_ML_Syntax.Private
                                 | FStar_Syntax_Syntax.NoExtract  ->
                                     FStar_Pervasives_Native.Some
                                       FStar_Extraction_ML_Syntax.NoExtract
                                 | uu____2539 -> FStar_Pervasives_Native.None)
                              quals in
                          let flags' =
                            FStar_List.choose
                              (fun uu___156_2547  ->
                                 match uu___156_2547 with
                                 | {
                                     FStar_Syntax_Syntax.n =
                                       FStar_Syntax_Syntax.Tm_constant
                                       (FStar_Const.Const_string
                                       (data,uu____2555));
                                     FStar_Syntax_Syntax.tk = uu____2556;
                                     FStar_Syntax_Syntax.pos = uu____2557;
                                     FStar_Syntax_Syntax.vars = uu____2558;_}
                                     ->
                                     FStar_Pervasives_Native.Some
                                       (FStar_Extraction_ML_Syntax.Attribute
                                          (FStar_Util.string_of_unicode data))
                                 | uu____2567 ->
                                     (FStar_Util.print_warning
                                        "Warning: unrecognized, non-string attribute, bother protz for a better error message";
                                      FStar_Pervasives_Native.None)) attrs in
                          let uu____2573 =
                            let uu____2576 =
                              let uu____2577 =
                                FStar_Extraction_ML_Util.mlloc_of_range
                                  se.FStar_Syntax_Syntax.sigrng in
                              FStar_Extraction_ML_Syntax.MLM_Loc uu____2577 in
                            [uu____2576;
                            FStar_Extraction_ML_Syntax.MLM_Let
                              (flavor, (FStar_List.append flags flags'),
                                (FStar_List.rev ml_lbs'))] in
                          (g1, uu____2573))
                 | uu____2584 ->
                     let uu____2585 =
                       let uu____2586 =
                         FStar_Extraction_ML_Code.string_of_mlexpr
                           g.FStar_Extraction_ML_UEnv.currentModule ml_let in
                       FStar_Util.format1
                         "Impossible: Translated a let to a non-let: %s"
                         uu____2586 in
                     failwith uu____2585))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____2594,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____2599 =
             FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption) in
           if uu____2599
           then
             let always_fail =
               let imp =
                 let uu____2610 = FStar_Syntax_Util.arrow_formals t in
                 match uu____2610 with
                 | ([],t1) ->
                     let b =
                       let uu____2645 =
                         FStar_Syntax_Syntax.gen_bv "_"
                           FStar_Pervasives_Native.None t1 in
                       FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                         uu____2645 in
                     let uu____2646 = fail_exp lid t1 in
                     FStar_Syntax_Util.abs [b] uu____2646
                       FStar_Pervasives_Native.None
                 | (bs,t1) ->
                     let uu____2679 = fail_exp lid t1 in
                     FStar_Syntax_Util.abs bs uu____2679
                       FStar_Pervasives_Native.None in
               let uu___160_2690 = se in
               let uu____2691 =
                 let uu____2692 =
                   let uu____2703 =
                     let uu____2710 =
                       let uu____2713 =
                         let uu____2714 =
                           let uu____2719 =
                             FStar_Syntax_Syntax.lid_as_fv lid
                               FStar_Syntax_Syntax.Delta_constant
                               FStar_Pervasives_Native.None in
                           FStar_Util.Inr uu____2719 in
                         {
                           FStar_Syntax_Syntax.lbname = uu____2714;
                           FStar_Syntax_Syntax.lbunivs = [];
                           FStar_Syntax_Syntax.lbtyp = t;
                           FStar_Syntax_Syntax.lbeff =
                             FStar_Parser_Const.effect_ML_lid;
                           FStar_Syntax_Syntax.lbdef = imp
                         } in
                       [uu____2713] in
                     (false, uu____2710) in
                   (uu____2703, [], []) in
                 FStar_Syntax_Syntax.Sig_let uu____2692 in
               {
                 FStar_Syntax_Syntax.sigel = uu____2691;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___160_2690.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___160_2690.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___160_2690.FStar_Syntax_Syntax.sigmeta)
               } in
             let uu____2732 = extract_sig g always_fail in
             (match uu____2732 with
              | (g1,mlm) ->
                  let uu____2751 =
                    FStar_Util.find_map quals
                      (fun uu___157_2754  ->
                         match uu___157_2754 with
                         | FStar_Syntax_Syntax.Discriminator l ->
                             FStar_Pervasives_Native.Some l
                         | uu____2758 -> FStar_Pervasives_Native.None) in
                  (match uu____2751 with
                   | FStar_Pervasives_Native.Some l ->
                       let uu____2766 =
                         let uu____2769 =
                           let uu____2770 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____2770 in
                         let uu____2771 =
                           let uu____2774 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l in
                           [uu____2774] in
                         uu____2769 :: uu____2771 in
                       (g1, uu____2766)
                   | uu____2777 ->
                       let uu____2780 =
                         FStar_Util.find_map quals
                           (fun uu___158_2783  ->
                              match uu___158_2783 with
                              | FStar_Syntax_Syntax.Projector (l,uu____2787)
                                  -> FStar_Pervasives_Native.Some l
                              | uu____2788 -> FStar_Pervasives_Native.None) in
                       (match uu____2780 with
                        | FStar_Pervasives_Native.Some uu____2795 -> (g1, [])
                        | uu____2798 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____2807 = FStar_Extraction_ML_Term.term_as_mlexpr g e in
           (match uu____2807 with
            | (ml_main,uu____2821,uu____2822) ->
                let uu____2823 =
                  let uu____2826 =
                    let uu____2827 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____2827 in
                  [uu____2826; FStar_Extraction_ML_Syntax.MLM_Top ml_main] in
                (g, uu____2823))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____2830 ->
           failwith "impossible -- removed by tc.fs"
       | FStar_Syntax_Syntax.Sig_assume uu____2837 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____2844 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____2847 -> (g, [])
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (if p = FStar_Syntax_Syntax.LightOff
            then FStar_Options.set_ml_ish ()
            else ();
            (g, [])))
let extract_iface:
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.modul -> env_t =
  fun g  ->
    fun m  ->
      let uu____2873 =
        FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____2873 FStar_Pervasives_Native.fst
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
      (let uu____2916 = FStar_Options.debug_any () in
       if uu____2916
       then
         let uu____2917 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
         FStar_Util.print1 "Extracting module %s\n" uu____2917
       else ());
      (let uu____2919 = FStar_Options.restore_cmd_line_options true in
       let name =
         FStar_Extraction_ML_Syntax.mlpath_of_lident
           m.FStar_Syntax_Syntax.name in
       let g1 =
         let uu___161_2922 = g in
         let uu____2923 =
           FStar_TypeChecker_Env.set_current_module
             g.FStar_Extraction_ML_UEnv.tcenv m.FStar_Syntax_Syntax.name in
         {
           FStar_Extraction_ML_UEnv.tcenv = uu____2923;
           FStar_Extraction_ML_UEnv.gamma =
             (uu___161_2922.FStar_Extraction_ML_UEnv.gamma);
           FStar_Extraction_ML_UEnv.tydefs =
             (uu___161_2922.FStar_Extraction_ML_UEnv.tydefs);
           FStar_Extraction_ML_UEnv.type_names =
             (uu___161_2922.FStar_Extraction_ML_UEnv.type_names);
           FStar_Extraction_ML_UEnv.currentModule = name
         } in
       let uu____2924 =
         FStar_Util.fold_map extract_sig g1
           m.FStar_Syntax_Syntax.declarations in
       match uu____2924 with
       | (g2,sigs) ->
           let mlm = FStar_List.flatten sigs in
           let is_kremlin =
             let uu____2953 = FStar_Options.codegen () in
             match uu____2953 with
             | FStar_Pervasives_Native.Some "Kremlin" -> true
             | uu____2956 -> false in
           let uu____2959 =
             (((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
                (is_kremlin ||
                   (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)))
               &&
               (FStar_Options.should_extract
                  (m.FStar_Syntax_Syntax.name).FStar_Ident.str) in
           if uu____2959
           then
             ((let uu____2967 =
                 FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
               FStar_Util.print1 "Extracted module %s\n" uu____2967);
              (g2,
                [FStar_Extraction_ML_Syntax.MLLib
                   [(name, (FStar_Pervasives_Native.Some ([], mlm)),
                      (FStar_Extraction_ML_Syntax.MLLib []))]]))
           else (g2, []))