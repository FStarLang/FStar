open Prims
let fail_exp lid t =
  let uu____15 =
    let uu____18 =
      let uu____19 =
        let uu____29 =
          FStar_Syntax_Syntax.fvar FStar_Syntax_Const.failwith_lid
            FStar_Syntax_Syntax.Delta_constant None in
        let uu____30 =
          let uu____32 = FStar_Syntax_Syntax.iarg t in
          let uu____33 =
            let uu____35 =
              let uu____36 =
                let uu____37 =
                  let uu____40 =
                    let uu____41 =
                      let uu____42 =
                        let uu____46 =
                          let uu____47 =
                            let uu____48 =
                              FStar_Syntax_Print.lid_to_string lid in
                            Prims.strcat "Not yet implemented:" uu____48 in
                          FStar_Bytes.string_as_unicode_bytes uu____47 in
                        (uu____46, FStar_Range.dummyRange) in
                      FStar_Const.Const_string uu____42 in
                    FStar_Syntax_Syntax.Tm_constant uu____41 in
                  FStar_Syntax_Syntax.mk uu____40 in
                uu____37 None FStar_Range.dummyRange in
              FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____36 in
            [uu____35] in
          uu____32 :: uu____33 in
        (uu____29, uu____30) in
      FStar_Syntax_Syntax.Tm_app uu____19 in
    FStar_Syntax_Syntax.mk uu____18 in
  uu____15 None FStar_Range.dummyRange
let mangle_projector_lid: FStar_Ident.lident -> FStar_Ident.lident =
  fun x  -> x
let lident_as_mlsymbol: FStar_Ident.lident -> Prims.string =
  fun id  -> (id.FStar_Ident.ident).FStar_Ident.idText
let as_pair uu___148_81 =
  match uu___148_81 with
  | a::b::[] -> (a, b)
  | uu____85 -> failwith "Expected a list with 2 elements"
let binders_as_mlty_binders env bs =
  FStar_Util.fold_map
    (fun env1  ->
       fun uu____117  ->
         match uu____117 with
         | (bv,uu____125) ->
             let uu____126 =
               let uu____127 =
                 let uu____129 =
                   let uu____130 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv in
                   FStar_Extraction_ML_Syntax.MLTY_Var uu____130 in
                 Some uu____129 in
               FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____127 in
             let uu____131 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv in
             (uu____126, uu____131)) env bs
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
            let uu____159 =
              let uu____160 = FStar_Syntax_Subst.compress def in
              FStar_All.pipe_right uu____160 FStar_Syntax_Util.unmeta in
            FStar_All.pipe_right uu____159 FStar_Syntax_Util.un_uinst in
          let def2 =
            match def1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs uu____162 ->
                FStar_Extraction_ML_Term.normalize_abs def1
            | uu____177 -> def1 in
          let uu____178 =
            match def2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____185) ->
                FStar_Syntax_Subst.open_term bs body
            | uu____208 -> ([], def2) in
          match uu____178 with
          | (bs,body) ->
              let assumed =
                FStar_Util.for_some
                  (fun uu___149_220  ->
                     match uu___149_220 with
                     | FStar_Syntax_Syntax.Assumption  -> true
                     | uu____221 -> false) quals in
              let uu____222 = binders_as_mlty_binders env bs in
              (match uu____222 with
               | (env1,ml_bs) ->
                   let body1 =
                     let uu____240 =
                       FStar_Extraction_ML_Term.term_as_mlty env1 body in
                     FStar_All.pipe_right uu____240
                       (FStar_Extraction_ML_Util.eraseTypeDeep
                          (FStar_Extraction_ML_Util.udelta_unfold env1)) in
                   let mangled_projector =
                     let uu____243 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___150_245  ->
                               match uu___150_245 with
                               | FStar_Syntax_Syntax.Projector uu____246 ->
                                   true
                               | uu____249 -> false)) in
                     if uu____243
                     then
                       let mname = mangle_projector_lid lid in
                       Some ((mname.FStar_Ident.ident).FStar_Ident.idText)
                     else None in
                   let td =
                     let uu____265 =
                       let uu____276 = lident_as_mlsymbol lid in
                       (assumed, uu____276, mangled_projector, ml_bs,
                         (Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1))) in
                     [uu____265] in
                   let def3 =
                     let uu____304 =
                       let uu____305 =
                         FStar_Extraction_ML_Util.mlloc_of_range
                           (FStar_Ident.range_of_lid lid) in
                       FStar_Extraction_ML_Syntax.MLM_Loc uu____305 in
                     [uu____304; FStar_Extraction_ML_Syntax.MLM_Ty td] in
                   let env2 =
                     let uu____307 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___151_309  ->
                               match uu___151_309 with
                               | FStar_Syntax_Syntax.Assumption  -> true
                               | FStar_Syntax_Syntax.New  -> true
                               | uu____310 -> false)) in
                     if uu____307
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
    let uu____371 = FStar_Syntax_Print.lid_to_string i.iname in
    let uu____372 = FStar_Syntax_Print.binders_to_string " " i.iparams in
    let uu____373 = FStar_Syntax_Print.term_to_string i.ityp in
    let uu____374 =
      let uu____375 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let uu____380 = FStar_Syntax_Print.lid_to_string d.dname in
                let uu____381 =
                  let uu____382 = FStar_Syntax_Print.term_to_string d.dtyp in
                  Prims.strcat " : " uu____382 in
                Prims.strcat uu____380 uu____381)) in
      FStar_All.pipe_right uu____375 (FStar_String.concat "\n\t\t") in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____371 uu____372 uu____373
      uu____374
let bundle_as_inductive_families env ses quals =
  FStar_All.pipe_right ses
    (FStar_List.collect
       (fun se  ->
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_inductive_typ (l,_us,bs,t,_mut_i,datas)
              ->
              let uu____420 = FStar_Syntax_Subst.open_term bs t in
              (match uu____420 with
               | (bs1,t1) ->
                   let datas1 =
                     FStar_All.pipe_right ses
                       (FStar_List.collect
                          (fun se1  ->
                             match se1.FStar_Syntax_Syntax.sigel with
                             | FStar_Syntax_Syntax.Sig_datacon
                                 (d,uu____433,t2,l',nparams,uu____437) when
                                 FStar_Ident.lid_equals l l' ->
                                 let uu____440 =
                                   FStar_Syntax_Util.arrow_formals t2 in
                                 (match uu____440 with
                                  | (bs',body) ->
                                      let uu____461 =
                                        FStar_Util.first_N
                                          (FStar_List.length bs1) bs' in
                                      (match uu____461 with
                                       | (bs_params,rest) ->
                                           let subst1 =
                                             FStar_List.map2
                                               (fun uu____499  ->
                                                  fun uu____500  ->
                                                    match (uu____499,
                                                            uu____500)
                                                    with
                                                    | ((b',uu____510),
                                                       (b,uu____512)) ->
                                                        let uu____517 =
                                                          let uu____522 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              b in
                                                          (b', uu____522) in
                                                        FStar_Syntax_Syntax.NT
                                                          uu____517)
                                               bs_params bs1 in
                                           let t3 =
                                             let uu____524 =
                                               let uu____527 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   body in
                                               FStar_Syntax_Util.arrow rest
                                                 uu____527 in
                                             FStar_All.pipe_right uu____524
                                               (FStar_Syntax_Subst.subst
                                                  subst1) in
                                           [{ dname = d; dtyp = t3 }]))
                             | uu____532 -> [])) in
                   [{
                      iname = l;
                      iparams = bs1;
                      ityp = t1;
                      idatas = datas1;
                      iquals = (se.FStar_Syntax_Syntax.sigquals)
                    }])
          | uu____533 -> []))
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
          let uu____570 =
            FStar_Extraction_ML_Term.term_as_mlty env1 ctor.dtyp in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env1) uu____570 in
        let tys = (ml_tyvars, mlt) in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp in
        let uu____581 =
          let uu____582 =
            FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false in
          fst uu____582 in
        let uu____585 =
          let uu____589 = lident_as_mlsymbol ctor.dname in
          let uu____590 = FStar_Extraction_ML_Util.argTypes mlt in
          (uu____589, uu____590) in
        (uu____581, uu____585) in
      let extract_one_family env1 ind =
        let uu____615 = binders_as_mlty_binders env1 ind.iparams in
        match uu____615 with
        | (env2,vars) ->
            let uu____641 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor vars) env2) in
            (match uu____641 with
             | (env3,ctors) ->
                 let uu____680 = FStar_Syntax_Util.arrow_formals ind.ityp in
                 (match uu____680 with
                  | (indices,uu____701) ->
                      let ml_params =
                        let uu____716 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____731  ->
                                    let uu____734 =
                                      let uu____735 =
                                        FStar_Util.string_of_int i in
                                      Prims.strcat "'dummyV" uu____735 in
                                    (uu____734, (Prims.parse_int "0")))) in
                        FStar_List.append vars uu____716 in
                      let tbody =
                        let uu____739 =
                          FStar_Util.find_opt
                            (fun uu___152_741  ->
                               match uu___152_741 with
                               | FStar_Syntax_Syntax.RecordType uu____742 ->
                                   true
                               | uu____747 -> false) ind.iquals in
                        match uu____739 with
                        | Some (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____754 = FStar_List.hd ctors in
                            (match uu____754 with
                             | (uu____761,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id  ->
                                        fun ty  ->
                                          let lid =
                                            FStar_Ident.lid_of_ids
                                              (FStar_List.append ns [id]) in
                                          let uu____775 =
                                            lident_as_mlsymbol lid in
                                          (uu____775, ty)) ids c_ty in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____776 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors in
                      let uu____778 =
                        let uu____789 = lident_as_mlsymbol ind.iname in
                        (false, uu____789, None, ml_params, (Some tbody)) in
                      (env3, uu____778))) in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____810,t,uu____812,uu____813,uu____814);
            FStar_Syntax_Syntax.sigrng = uu____815;
            FStar_Syntax_Syntax.sigquals = uu____816;
            FStar_Syntax_Syntax.sigmeta = uu____817;_}::[],uu____818),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____826 = extract_ctor [] env { dname = l; dtyp = t } in
          (match uu____826 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____847),quals) ->
          let ifams = bundle_as_inductive_families env ses quals in
          let uu____858 = FStar_Util.fold_map extract_one_family env ifams in
          (match uu____858 with
           | (env1,td) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Ty td]))
      | uu____910 -> failwith "Unexpected signature element"
let rec extract_sig:
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t* FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
  =
  fun g  ->
    fun se  ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u  ->
           let uu____931 = FStar_Syntax_Print.sigelt_to_string se in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____931);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____935 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____940 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____949 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
           ->
           let extend_env g1 lid ml_name tm tysc =
             let uu____977 =
               let uu____980 =
                 FStar_Syntax_Syntax.lid_as_fv lid
                   FStar_Syntax_Syntax.Delta_equational None in
               FStar_Extraction_ML_UEnv.extend_fv' g1 uu____980 ml_name tysc
                 false false in
             match uu____977 with
             | (g2,mangled_name) ->
                 ((let uu____986 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          g2.FStar_Extraction_ML_UEnv.tcenv)
                       (FStar_Options.Other "ExtractionReify") in
                   if uu____986
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
             (let uu____998 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify") in
              if uu____998
              then
                let uu____999 = FStar_Syntax_Print.term_to_string tm in
                FStar_Util.print1 "extract_fv term: %s\n" uu____999
              else ());
             (let uu____1001 =
                let uu____1002 = FStar_Syntax_Subst.compress tm in
                uu____1002.FStar_Syntax_Syntax.n in
              match uu____1001 with
              | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____1008) ->
                  extract_fv tm1
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let mlp =
                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  let uu____1019 =
                    let uu____1024 = FStar_Extraction_ML_UEnv.lookup_fv g fv in
                    FStar_All.pipe_left FStar_Util.right uu____1024 in
                  (match uu____1019 with
                   | (uu____1053,uu____1054,tysc,uu____1056) ->
                       let uu____1057 =
                         FStar_All.pipe_left
                           (FStar_Extraction_ML_Syntax.with_ty
                              FStar_Extraction_ML_Syntax.MLTY_Top)
                           (FStar_Extraction_ML_Syntax.MLE_Name mlp) in
                       (uu____1057, tysc))
              | uu____1058 -> failwith "Not an fv") in
           let extract_action g1 a =
             (let uu____1074 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g1.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify") in
              if uu____1074
              then
                let uu____1075 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_typ in
                let uu____1076 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_defn in
                FStar_Util.print2 "Action type %s and term %s\n" uu____1075
                  uu____1076
              else ());
             (let uu____1078 = FStar_Extraction_ML_UEnv.action_name ed a in
              match uu____1078 with
              | (a_nm,a_lid) ->
                  let lbname =
                    let uu____1088 =
                      FStar_Syntax_Syntax.new_bv
                        (Some
                           ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                        FStar_Syntax_Syntax.tun in
                    FStar_Util.Inl uu____1088 in
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
                  let uu____1111 =
                    FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb in
                  (match uu____1111 with
                   | (a_let,uu____1118,ty) ->
                       ((let uu____1121 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug
                                g1.FStar_Extraction_ML_UEnv.tcenv)
                             (FStar_Options.Other "ExtractionReify") in
                         if uu____1121
                         then
                           let uu____1122 =
                             FStar_Extraction_ML_Code.string_of_mlexpr a_nm
                               a_let in
                           FStar_Util.print1 "Extracted action term: %s\n"
                             uu____1122
                         else ());
                        (let uu____1124 =
                           match a_let.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_Let
                               ((uu____1129,uu____1130,mllb::[]),uu____1132)
                               ->
                               (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                                with
                                | Some tysc ->
                                    ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                      tysc)
                                | None  -> failwith "No type scheme")
                           | uu____1143 -> failwith "Impossible" in
                         match uu____1124 with
                         | (exp,tysc) ->
                             ((let uu____1151 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug
                                      g1.FStar_Extraction_ML_UEnv.tcenv)
                                   (FStar_Options.Other "ExtractionReify") in
                               if uu____1151
                               then
                                 ((let uu____1153 =
                                     FStar_Extraction_ML_Code.string_of_mlty
                                       a_nm (snd tysc) in
                                   FStar_Util.print1
                                     "Extracted action type: %s\n" uu____1153);
                                  FStar_List.iter
                                    (fun x  ->
                                       FStar_Util.print1 "and binders: %s\n"
                                         (fst x)) (fst tysc))
                               else ());
                              extend_env g1 a_lid a_nm exp tysc))))) in
           let uu____1160 =
             let uu____1163 =
               extract_fv (snd ed.FStar_Syntax_Syntax.return_repr) in
             match uu____1163 with
             | (return_tm,ty_sc) ->
                 let uu____1171 =
                   FStar_Extraction_ML_UEnv.monad_op_name ed "return" in
                 (match uu____1171 with
                  | (return_nm,return_lid) ->
                      extend_env g return_lid return_nm return_tm ty_sc) in
           (match uu____1160 with
            | (g1,return_decl) ->
                let uu____1183 =
                  let uu____1186 =
                    extract_fv (snd ed.FStar_Syntax_Syntax.bind_repr) in
                  match uu____1186 with
                  | (bind_tm,ty_sc) ->
                      let uu____1194 =
                        FStar_Extraction_ML_UEnv.monad_op_name ed "bind" in
                      (match uu____1194 with
                       | (bind_nm,bind_lid) ->
                           extend_env g1 bind_lid bind_nm bind_tm ty_sc) in
                (match uu____1183 with
                 | (g2,bind_decl) ->
                     let uu____1206 =
                       FStar_Util.fold_map extract_action g2
                         ed.FStar_Syntax_Syntax.actions in
                     (match uu____1206 with
                      | (g3,actions) ->
                          (g3,
                            (FStar_List.append [return_decl; bind_decl]
                               actions)))))
       | FStar_Syntax_Syntax.Sig_new_effect uu____1218 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____1221,t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____1225 =
             let uu____1226 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___153_1228  ->
                       match uu___153_1228 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____1229 -> false)) in
             Prims.op_Negation uu____1226 in
           if uu____1225
           then (g, [])
           else
             (let uu____1235 = FStar_Syntax_Util.arrow_formals t in
              match uu____1235 with
              | (bs,uu____1247) ->
                  let fv =
                    FStar_Syntax_Syntax.lid_as_fv lid
                      FStar_Syntax_Syntax.Delta_constant None in
                  let uu____1259 =
                    FStar_Syntax_Util.abs bs FStar_TypeChecker_Common.t_unit
                      None in
                  extract_typ_abbrev g fv quals uu____1259)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____1266,uu____1267)
           when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____1278 =
             let uu____1283 =
               FStar_TypeChecker_Env.open_universes_in
                 g.FStar_Extraction_ML_UEnv.tcenv
                 lb.FStar_Syntax_Syntax.lbunivs
                 [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp] in
             match uu____1283 with
             | (tcenv,uu____1299,def_typ) ->
                 let uu____1303 = as_pair def_typ in (tcenv, uu____1303) in
           (match uu____1278 with
            | (tcenv,(lbdef,lbtyp)) ->
                let lbtyp1 =
                  FStar_TypeChecker_Normalize.unfold_whnf tcenv lbtyp in
                let lbdef1 =
                  FStar_TypeChecker_Normalize.eta_expand_with_type tcenv
                    lbdef lbtyp1 in
                let uu____1318 =
                  FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                extract_typ_abbrev g uu____1318 quals lbdef1)
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____1320,attrs) ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let elet =
             FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_let
                  (lbs, FStar_Syntax_Const.exp_false_bool)) None
               se.FStar_Syntax_Syntax.sigrng in
           let uu____1335 = FStar_Extraction_ML_Term.term_as_mlexpr g elet in
           (match uu____1335 with
            | (ml_let,uu____1343,uu____1344) ->
                (match ml_let.FStar_Extraction_ML_Syntax.expr with
                 | FStar_Extraction_ML_Syntax.MLE_Let
                     ((flavor,uu____1349,bindings),uu____1351) ->
                     let uu____1358 =
                       FStar_List.fold_left2
                         (fun uu____1365  ->
                            fun ml_lb  ->
                              fun uu____1367  ->
                                match (uu____1365, uu____1367) with
                                | ((env,ml_lbs),{
                                                  FStar_Syntax_Syntax.lbname
                                                    = lbname;
                                                  FStar_Syntax_Syntax.lbunivs
                                                    = uu____1380;
                                                  FStar_Syntax_Syntax.lbtyp =
                                                    t;
                                                  FStar_Syntax_Syntax.lbeff =
                                                    uu____1382;
                                                  FStar_Syntax_Syntax.lbdef =
                                                    uu____1383;_})
                                    ->
                                    let lb_lid =
                                      let uu____1397 =
                                        let uu____1402 =
                                          FStar_Util.right lbname in
                                        uu____1402.FStar_Syntax_Syntax.fv_name in
                                      uu____1397.FStar_Syntax_Syntax.v in
                                    let uu____1406 =
                                      let uu____1409 =
                                        FStar_All.pipe_right quals
                                          (FStar_Util.for_some
                                             (fun uu___154_1411  ->
                                                match uu___154_1411 with
                                                | FStar_Syntax_Syntax.Projector
                                                    uu____1412 -> true
                                                | uu____1415 -> false)) in
                                      if uu____1409
                                      then
                                        let mname =
                                          let uu____1419 =
                                            mangle_projector_lid lb_lid in
                                          FStar_All.pipe_right uu____1419
                                            FStar_Extraction_ML_Syntax.mlpath_of_lident in
                                        let uu____1420 =
                                          let uu____1423 =
                                            FStar_Util.right lbname in
                                          let uu____1424 =
                                            FStar_Util.must
                                              ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc in
                                          FStar_Extraction_ML_UEnv.extend_fv'
                                            env uu____1423 mname uu____1424
                                            ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                            false in
                                        match uu____1420 with
                                        | (env1,uu____1428) ->
                                            (env1,
                                              (let uu___159_1429 = ml_lb in
                                               {
                                                 FStar_Extraction_ML_Syntax.mllb_name
                                                   =
                                                   ((snd mname),
                                                     (Prims.parse_int "0"));
                                                 FStar_Extraction_ML_Syntax.mllb_tysc
                                                   =
                                                   (uu___159_1429.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                 FStar_Extraction_ML_Syntax.mllb_add_unit
                                                   =
                                                   (uu___159_1429.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                 FStar_Extraction_ML_Syntax.mllb_def
                                                   =
                                                   (uu___159_1429.FStar_Extraction_ML_Syntax.mllb_def);
                                                 FStar_Extraction_ML_Syntax.print_typ
                                                   =
                                                   (uu___159_1429.FStar_Extraction_ML_Syntax.print_typ)
                                               }))
                                      else
                                        (let uu____1432 =
                                           let uu____1433 =
                                             let uu____1436 =
                                               FStar_Util.must
                                                 ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc in
                                             FStar_Extraction_ML_UEnv.extend_lb
                                               env lbname t uu____1436
                                               ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                               false in
                                           FStar_All.pipe_left
                                             FStar_Pervasives.fst uu____1433 in
                                         (uu____1432, ml_lb)) in
                                    (match uu____1406 with
                                     | (g1,ml_lb1) ->
                                         (g1, (ml_lb1 :: ml_lbs)))) (g, [])
                         bindings (snd lbs) in
                     (match uu____1358 with
                      | (g1,ml_lbs') ->
                          let flags =
                            FStar_List.choose
                              (fun uu___155_1456  ->
                                 match uu___155_1456 with
                                 | FStar_Syntax_Syntax.Assumption  ->
                                     Some FStar_Extraction_ML_Syntax.Assumed
                                 | FStar_Syntax_Syntax.Private  ->
                                     Some FStar_Extraction_ML_Syntax.Private
                                 | FStar_Syntax_Syntax.NoExtract  ->
                                     Some
                                       FStar_Extraction_ML_Syntax.NoExtract
                                 | uu____1458 -> None) quals in
                          let flags' =
                            FStar_List.choose
                              (fun uu___156_1463  ->
                                 match uu___156_1463 with
                                 | {
                                     FStar_Syntax_Syntax.n =
                                       FStar_Syntax_Syntax.Tm_constant
                                       (FStar_Const.Const_string
                                       (data,uu____1468));
                                     FStar_Syntax_Syntax.tk = uu____1469;
                                     FStar_Syntax_Syntax.pos = uu____1470;
                                     FStar_Syntax_Syntax.vars = uu____1471;_}
                                     ->
                                     Some
                                       (FStar_Extraction_ML_Syntax.Attribute
                                          (FStar_Util.string_of_unicode data))
                                 | uu____1476 ->
                                     (FStar_Util.print_warning
                                        "Warning: unrecognized, non-string attribute, bother protz for a better error message";
                                      None)) attrs in
                          let uu____1480 =
                            let uu____1482 =
                              let uu____1483 =
                                FStar_Extraction_ML_Util.mlloc_of_range
                                  se.FStar_Syntax_Syntax.sigrng in
                              FStar_Extraction_ML_Syntax.MLM_Loc uu____1483 in
                            [uu____1482;
                            FStar_Extraction_ML_Syntax.MLM_Let
                              (flavor, (FStar_List.append flags flags'),
                                (FStar_List.rev ml_lbs'))] in
                          (g1, uu____1480))
                 | uu____1487 ->
                     let uu____1488 =
                       let uu____1489 =
                         FStar_Extraction_ML_Code.string_of_mlexpr
                           g.FStar_Extraction_ML_UEnv.currentModule ml_let in
                       FStar_Util.format1
                         "Impossible: Translated a let to a non-let: %s"
                         uu____1489 in
                     failwith uu____1488))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____1494,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____1498 =
             FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption) in
           if uu____1498
           then
             let always_fail =
               let imp =
                 let uu____1505 = FStar_Syntax_Util.arrow_formals t in
                 match uu____1505 with
                 | ([],t1) ->
                     let b =
                       let uu____1524 =
                         FStar_Syntax_Syntax.gen_bv "_" None t1 in
                       FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                         uu____1524 in
                     let uu____1525 = fail_exp lid t1 in
                     FStar_Syntax_Util.abs [b] uu____1525 None
                 | (bs,t1) ->
                     let uu____1543 = fail_exp lid t1 in
                     FStar_Syntax_Util.abs bs uu____1543 None in
               let uu___160_1549 = se in
               let uu____1550 =
                 let uu____1551 =
                   let uu____1557 =
                     let uu____1561 =
                       let uu____1563 =
                         let uu____1564 =
                           let uu____1567 =
                             FStar_Syntax_Syntax.lid_as_fv lid
                               FStar_Syntax_Syntax.Delta_constant None in
                           FStar_Util.Inr uu____1567 in
                         {
                           FStar_Syntax_Syntax.lbname = uu____1564;
                           FStar_Syntax_Syntax.lbunivs = [];
                           FStar_Syntax_Syntax.lbtyp = t;
                           FStar_Syntax_Syntax.lbeff =
                             FStar_Syntax_Const.effect_ML_lid;
                           FStar_Syntax_Syntax.lbdef = imp
                         } in
                       [uu____1563] in
                     (false, uu____1561) in
                   (uu____1557, [], []) in
                 FStar_Syntax_Syntax.Sig_let uu____1551 in
               {
                 FStar_Syntax_Syntax.sigel = uu____1550;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___160_1549.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___160_1549.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___160_1549.FStar_Syntax_Syntax.sigmeta)
               } in
             let uu____1574 = extract_sig g always_fail in
             (match uu____1574 with
              | (g1,mlm) ->
                  let uu____1585 =
                    FStar_Util.find_map quals
                      (fun uu___157_1587  ->
                         match uu___157_1587 with
                         | FStar_Syntax_Syntax.Discriminator l -> Some l
                         | uu____1590 -> None) in
                  (match uu____1585 with
                   | Some l ->
                       let uu____1595 =
                         let uu____1597 =
                           let uu____1598 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____1598 in
                         let uu____1599 =
                           let uu____1601 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l in
                           [uu____1601] in
                         uu____1597 :: uu____1599 in
                       (g1, uu____1595)
                   | uu____1603 ->
                       let uu____1605 =
                         FStar_Util.find_map quals
                           (fun uu___158_1607  ->
                              match uu___158_1607 with
                              | FStar_Syntax_Syntax.Projector (l,uu____1610)
                                  -> Some l
                              | uu____1611 -> None) in
                       (match uu____1605 with
                        | Some uu____1615 -> (g1, [])
                        | uu____1617 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____1623 = FStar_Extraction_ML_Term.term_as_mlexpr g e in
           (match uu____1623 with
            | (ml_main,uu____1631,uu____1632) ->
                let uu____1633 =
                  let uu____1635 =
                    let uu____1636 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____1636 in
                  [uu____1635; FStar_Extraction_ML_Syntax.MLM_Top ml_main] in
                (g, uu____1633))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____1638 ->
           failwith "impossible -- removed by tc.fs"
       | FStar_Syntax_Syntax.Sig_assume uu____1642 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____1646 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____1648 -> (g, [])
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (if p = FStar_Syntax_Syntax.LightOff
            then FStar_Options.set_ml_ish ()
            else ();
            (g, [])))
let extract_iface:
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.modul -> env_t =
  fun g  ->
    fun m  ->
      let uu____1666 =
        FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____1666 FStar_Pervasives.fst
let extract:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Extraction_ML_UEnv.env* FStar_Extraction_ML_Syntax.mllib
        Prims.list)
  =
  fun g  ->
    fun m  ->
      FStar_Syntax_Syntax.reset_gensym ();
      (let uu____1692 = FStar_Options.debug_any () in
       if uu____1692
       then
         let uu____1693 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
         FStar_Util.print1 "Extracting module %s\n" uu____1693
       else ());
      (let uu____1695 = FStar_Options.restore_cmd_line_options true in
       let name =
         FStar_Extraction_ML_Syntax.mlpath_of_lident
           m.FStar_Syntax_Syntax.name in
       let g1 =
         let uu___161_1698 = g in
         {
           FStar_Extraction_ML_UEnv.tcenv =
             (uu___161_1698.FStar_Extraction_ML_UEnv.tcenv);
           FStar_Extraction_ML_UEnv.gamma =
             (uu___161_1698.FStar_Extraction_ML_UEnv.gamma);
           FStar_Extraction_ML_UEnv.tydefs =
             (uu___161_1698.FStar_Extraction_ML_UEnv.tydefs);
           FStar_Extraction_ML_UEnv.currentModule = name
         } in
       let uu____1699 =
         FStar_Util.fold_map extract_sig g1
           m.FStar_Syntax_Syntax.declarations in
       match uu____1699 with
       | (g2,sigs) ->
           let mlm = FStar_List.flatten sigs in
           let is_kremlin =
             let uu____1716 = FStar_Options.codegen () in
             match uu____1716 with
             | Some "Kremlin" -> true
             | uu____1718 -> false in
           let uu____1720 =
             (((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
                (is_kremlin ||
                   (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)))
               &&
               (FStar_Options.should_extract
                  (m.FStar_Syntax_Syntax.name).FStar_Ident.str) in
           if uu____1720
           then
             ((let uu____1725 =
                 FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
               FStar_Util.print1 "Extracted module %s\n" uu____1725);
              (g2,
                [FStar_Extraction_ML_Syntax.MLLib
                   [(name, (Some ([], mlm)),
                      (FStar_Extraction_ML_Syntax.MLLib []))]]))
           else (g2, []))