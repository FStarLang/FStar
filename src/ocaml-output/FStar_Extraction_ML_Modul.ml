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
let as_pair uu___149_81 =
  match uu___149_81 with
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
                  (fun uu___150_220  ->
                     match uu___150_220 with
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
                            (fun uu___151_245  ->
                               match uu___151_245 with
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
                            (fun uu___152_309  ->
                               match uu___152_309 with
                               | FStar_Syntax_Syntax.Assumption 
                                 |FStar_Syntax_Syntax.New  -> true
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
                                               (fun uu____497  ->
                                                  fun uu____498  ->
                                                    match (uu____497,
                                                            uu____498)
                                                    with
                                                    | ((b',uu____508),
                                                       (b,uu____510)) ->
                                                        let uu____515 =
                                                          let uu____520 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              b in
                                                          (b', uu____520) in
                                                        FStar_Syntax_Syntax.NT
                                                          uu____515)
                                               bs_params bs1 in
                                           let t3 =
                                             let uu____522 =
                                               let uu____525 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   body in
                                               FStar_Syntax_Util.arrow rest
                                                 uu____525 in
                                             FStar_All.pipe_right uu____522
                                               (FStar_Syntax_Subst.subst
                                                  subst1) in
                                           [{ dname = d; dtyp = t3 }]))
                             | uu____530 -> [])) in
                   [{
                      iname = l;
                      iparams = bs1;
                      ityp = t1;
                      idatas = datas1;
                      iquals = (se.FStar_Syntax_Syntax.sigquals)
                    }])
          | uu____531 -> []))
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
          let uu____568 =
            FStar_Extraction_ML_Term.term_as_mlty env1 ctor.dtyp in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env1) uu____568 in
        let tys = (ml_tyvars, mlt) in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp in
        let uu____579 =
          let uu____580 =
            FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false in
          fst uu____580 in
        let uu____583 =
          let uu____587 = lident_as_mlsymbol ctor.dname in
          let uu____588 = FStar_Extraction_ML_Util.argTypes mlt in
          (uu____587, uu____588) in
        (uu____579, uu____583) in
      let extract_one_family env1 ind =
        let uu____613 = binders_as_mlty_binders env1 ind.iparams in
        match uu____613 with
        | (env2,vars) ->
            let uu____639 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor vars) env2) in
            (match uu____639 with
             | (env3,ctors) ->
                 let uu____678 = FStar_Syntax_Util.arrow_formals ind.ityp in
                 (match uu____678 with
                  | (indices,uu____699) ->
                      let ml_params =
                        let uu____714 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____729  ->
                                    let uu____732 =
                                      let uu____733 =
                                        FStar_Util.string_of_int i in
                                      Prims.strcat "'dummyV" uu____733 in
                                    (uu____732, (Prims.parse_int "0")))) in
                        FStar_List.append vars uu____714 in
                      let tbody =
                        let uu____737 =
                          FStar_Util.find_opt
                            (fun uu___153_739  ->
                               match uu___153_739 with
                               | FStar_Syntax_Syntax.RecordType uu____740 ->
                                   true
                               | uu____745 -> false) ind.iquals in
                        match uu____737 with
                        | Some (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____752 = FStar_List.hd ctors in
                            (match uu____752 with
                             | (uu____759,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id  ->
                                        fun ty  ->
                                          let lid =
                                            FStar_Ident.lid_of_ids
                                              (FStar_List.append ns [id]) in
                                          let uu____773 =
                                            lident_as_mlsymbol lid in
                                          (uu____773, ty)) ids c_ty in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____774 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors in
                      let uu____776 =
                        let uu____787 = lident_as_mlsymbol ind.iname in
                        (false, uu____787, None, ml_params, (Some tbody)) in
                      (env3, uu____776))) in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____808,t,uu____810,uu____811,uu____812);
            FStar_Syntax_Syntax.sigrng = uu____813;
            FStar_Syntax_Syntax.sigquals = uu____814;
            FStar_Syntax_Syntax.sigmeta = uu____815;_}::[],uu____816),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____824 = extract_ctor [] env { dname = l; dtyp = t } in
          (match uu____824 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____845),quals) ->
          let ifams = bundle_as_inductive_families env ses quals in
          let uu____856 = FStar_Util.fold_map extract_one_family env ifams in
          (match uu____856 with
           | (env1,td) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Ty td]))
      | uu____908 -> failwith "Unexpected signature element"
let rec extract_sig:
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t* FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
  =
  fun g  ->
    fun se  ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u  ->
           let uu____929 = FStar_Syntax_Print.sigelt_to_string se in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____929);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle _
         |FStar_Syntax_Syntax.Sig_inductive_typ _
          |FStar_Syntax_Syntax.Sig_datacon _ -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
           ->
           let extend_env g1 lid ml_name tm tysc =
             let uu____956 =
               let uu____959 =
                 FStar_Syntax_Syntax.lid_as_fv lid
                   FStar_Syntax_Syntax.Delta_equational None in
               FStar_Extraction_ML_UEnv.extend_fv' g1 uu____959 ml_name tysc
                 false false in
             match uu____956 with
             | (g2,mangled_name) ->
                 ((let uu____965 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          g2.FStar_Extraction_ML_UEnv.tcenv)
                       (FStar_Options.Other "ExtractionReify") in
                   if uu____965
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
             (let uu____977 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify") in
              if uu____977
              then
                let uu____978 = FStar_Syntax_Print.term_to_string tm in
                FStar_Util.print1 "extract_fv term: %s\n" uu____978
              else ());
             (let uu____980 =
                let uu____981 = FStar_Syntax_Subst.compress tm in
                uu____981.FStar_Syntax_Syntax.n in
              match uu____980 with
              | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____987) ->
                  extract_fv tm1
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let mlp =
                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  let uu____998 =
                    let uu____1003 = FStar_Extraction_ML_UEnv.lookup_fv g fv in
                    FStar_All.pipe_left FStar_Util.right uu____1003 in
                  (match uu____998 with
                   | (uu____1032,uu____1033,tysc,uu____1035) ->
                       let uu____1036 =
                         FStar_All.pipe_left
                           (FStar_Extraction_ML_Syntax.with_ty
                              FStar_Extraction_ML_Syntax.MLTY_Top)
                           (FStar_Extraction_ML_Syntax.MLE_Name mlp) in
                       (uu____1036, tysc))
              | uu____1037 -> failwith "Not an fv") in
           let extract_action g1 a =
             (let uu____1053 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g1.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify") in
              if uu____1053
              then
                let uu____1054 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_typ in
                let uu____1055 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_defn in
                FStar_Util.print2 "Action type %s and term %s\n" uu____1054
                  uu____1055
              else ());
             (let uu____1057 = FStar_Extraction_ML_UEnv.action_name ed a in
              match uu____1057 with
              | (a_nm,a_lid) ->
                  let lbname =
                    let uu____1067 =
                      FStar_Syntax_Syntax.new_bv
                        (Some
                           ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                        FStar_Syntax_Syntax.tun in
                    FStar_Util.Inl uu____1067 in
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
                  let uu____1090 =
                    FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb in
                  (match uu____1090 with
                   | (a_let,uu____1097,ty) ->
                       ((let uu____1100 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug
                                g1.FStar_Extraction_ML_UEnv.tcenv)
                             (FStar_Options.Other "ExtractionReify") in
                         if uu____1100
                         then
                           let uu____1101 =
                             FStar_Extraction_ML_Code.string_of_mlexpr a_nm
                               a_let in
                           FStar_Util.print1 "Extracted action term: %s\n"
                             uu____1101
                         else ());
                        (let uu____1103 =
                           match a_let.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_Let
                               ((uu____1108,uu____1109,mllb::[]),uu____1111)
                               ->
                               (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                                with
                                | Some tysc ->
                                    ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                      tysc)
                                | None  -> failwith "No type scheme")
                           | uu____1122 -> failwith "Impossible" in
                         match uu____1103 with
                         | (exp,tysc) ->
                             ((let uu____1130 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug
                                      g1.FStar_Extraction_ML_UEnv.tcenv)
                                   (FStar_Options.Other "ExtractionReify") in
                               if uu____1130
                               then
                                 ((let uu____1132 =
                                     FStar_Extraction_ML_Code.string_of_mlty
                                       a_nm (snd tysc) in
                                   FStar_Util.print1
                                     "Extracted action type: %s\n" uu____1132);
                                  FStar_List.iter
                                    (fun x  ->
                                       FStar_Util.print1 "and binders: %s\n"
                                         (fst x)) (fst tysc))
                               else ());
                              extend_env g1 a_lid a_nm exp tysc))))) in
           let uu____1139 =
             let uu____1142 =
               extract_fv (snd ed.FStar_Syntax_Syntax.return_repr) in
             match uu____1142 with
             | (return_tm,ty_sc) ->
                 let uu____1150 =
                   FStar_Extraction_ML_UEnv.monad_op_name ed "return" in
                 (match uu____1150 with
                  | (return_nm,return_lid) ->
                      extend_env g return_lid return_nm return_tm ty_sc) in
           (match uu____1139 with
            | (g1,return_decl) ->
                let uu____1162 =
                  let uu____1165 =
                    extract_fv (snd ed.FStar_Syntax_Syntax.bind_repr) in
                  match uu____1165 with
                  | (bind_tm,ty_sc) ->
                      let uu____1173 =
                        FStar_Extraction_ML_UEnv.monad_op_name ed "bind" in
                      (match uu____1173 with
                       | (bind_nm,bind_lid) ->
                           extend_env g1 bind_lid bind_nm bind_tm ty_sc) in
                (match uu____1162 with
                 | (g2,bind_decl) ->
                     let uu____1185 =
                       FStar_Util.fold_map extract_action g2
                         ed.FStar_Syntax_Syntax.actions in
                     (match uu____1185 with
                      | (g3,actions) ->
                          (g3,
                            (FStar_List.append [return_decl; bind_decl]
                               actions)))))
       | FStar_Syntax_Syntax.Sig_new_effect uu____1197 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____1200,t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____1204 =
             let uu____1205 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___154_1207  ->
                       match uu___154_1207 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____1208 -> false)) in
             Prims.op_Negation uu____1205 in
           if uu____1204
           then (g, [])
           else
             (let uu____1214 = FStar_Syntax_Util.arrow_formals t in
              match uu____1214 with
              | (bs,uu____1226) ->
                  let fv =
                    FStar_Syntax_Syntax.lid_as_fv lid
                      FStar_Syntax_Syntax.Delta_constant None in
                  let uu____1238 =
                    FStar_Syntax_Util.abs bs FStar_TypeChecker_Common.t_unit
                      None in
                  extract_typ_abbrev g fv quals uu____1238)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____1245,uu____1246)
           when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____1257 =
             let uu____1262 =
               FStar_TypeChecker_Env.open_universes_in
                 g.FStar_Extraction_ML_UEnv.tcenv
                 lb.FStar_Syntax_Syntax.lbunivs
                 [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp] in
             match uu____1262 with
             | (tcenv,uu____1278,def_typ) ->
                 let uu____1282 = as_pair def_typ in (tcenv, uu____1282) in
           (match uu____1257 with
            | (tcenv,(lbdef,lbtyp)) ->
                let lbtyp1 =
                  FStar_TypeChecker_Normalize.unfold_whnf tcenv lbtyp in
                let lbdef1 =
                  FStar_TypeChecker_Normalize.eta_expand_with_type tcenv
                    lbdef lbtyp1 in
                let uu____1297 =
                  FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                extract_typ_abbrev g uu____1297 quals lbdef1)
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____1299,attrs) ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let elet =
             FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_let
                  (lbs, FStar_Syntax_Const.exp_false_bool)) None
               se.FStar_Syntax_Syntax.sigrng in
           let uu____1314 = FStar_Extraction_ML_Term.term_as_mlexpr g elet in
           (match uu____1314 with
            | (ml_let,uu____1322,uu____1323) ->
                (match ml_let.FStar_Extraction_ML_Syntax.expr with
                 | FStar_Extraction_ML_Syntax.MLE_Let
                     ((flavor,uu____1328,bindings),uu____1330) ->
                     let uu____1337 =
                       FStar_List.fold_left2
                         (fun uu____1344  ->
                            fun ml_lb  ->
                              fun uu____1346  ->
                                match (uu____1344, uu____1346) with
                                | ((env,ml_lbs),{
                                                  FStar_Syntax_Syntax.lbname
                                                    = lbname;
                                                  FStar_Syntax_Syntax.lbunivs
                                                    = uu____1359;
                                                  FStar_Syntax_Syntax.lbtyp =
                                                    t;
                                                  FStar_Syntax_Syntax.lbeff =
                                                    uu____1361;
                                                  FStar_Syntax_Syntax.lbdef =
                                                    uu____1362;_})
                                    ->
                                    let lb_lid =
                                      let uu____1376 =
                                        let uu____1381 =
                                          FStar_Util.right lbname in
                                        uu____1381.FStar_Syntax_Syntax.fv_name in
                                      uu____1376.FStar_Syntax_Syntax.v in
                                    let uu____1385 =
                                      let uu____1388 =
                                        FStar_All.pipe_right quals
                                          (FStar_Util.for_some
                                             (fun uu___155_1390  ->
                                                match uu___155_1390 with
                                                | FStar_Syntax_Syntax.Projector
                                                    uu____1391 -> true
                                                | uu____1394 -> false)) in
                                      if uu____1388
                                      then
                                        let mname =
                                          let uu____1398 =
                                            mangle_projector_lid lb_lid in
                                          FStar_All.pipe_right uu____1398
                                            FStar_Extraction_ML_Syntax.mlpath_of_lident in
                                        let uu____1399 =
                                          let uu____1402 =
                                            FStar_Util.right lbname in
                                          let uu____1403 =
                                            FStar_Util.must
                                              ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc in
                                          FStar_Extraction_ML_UEnv.extend_fv'
                                            env uu____1402 mname uu____1403
                                            ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                            false in
                                        match uu____1399 with
                                        | (env1,uu____1407) ->
                                            (env1,
                                              (let uu___160_1408 = ml_lb in
                                               {
                                                 FStar_Extraction_ML_Syntax.mllb_name
                                                   =
                                                   ((snd mname),
                                                     (Prims.parse_int "0"));
                                                 FStar_Extraction_ML_Syntax.mllb_tysc
                                                   =
                                                   (uu___160_1408.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                 FStar_Extraction_ML_Syntax.mllb_add_unit
                                                   =
                                                   (uu___160_1408.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                 FStar_Extraction_ML_Syntax.mllb_def
                                                   =
                                                   (uu___160_1408.FStar_Extraction_ML_Syntax.mllb_def);
                                                 FStar_Extraction_ML_Syntax.print_typ
                                                   =
                                                   (uu___160_1408.FStar_Extraction_ML_Syntax.print_typ)
                                               }))
                                      else
                                        (let uu____1411 =
                                           let uu____1412 =
                                             let uu____1415 =
                                               FStar_Util.must
                                                 ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc in
                                             FStar_Extraction_ML_UEnv.extend_lb
                                               env lbname t uu____1415
                                               ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                               false in
                                           FStar_All.pipe_left
                                             FStar_Pervasives.fst uu____1412 in
                                         (uu____1411, ml_lb)) in
                                    (match uu____1385 with
                                     | (g1,ml_lb1) ->
                                         (g1, (ml_lb1 :: ml_lbs)))) (g, [])
                         bindings (snd lbs) in
                     (match uu____1337 with
                      | (g1,ml_lbs') ->
                          let flags =
                            FStar_List.choose
                              (fun uu___156_1435  ->
                                 match uu___156_1435 with
                                 | FStar_Syntax_Syntax.Assumption  ->
                                     Some FStar_Extraction_ML_Syntax.Assumed
                                 | FStar_Syntax_Syntax.Private  ->
                                     Some FStar_Extraction_ML_Syntax.Private
                                 | FStar_Syntax_Syntax.NoExtract  ->
                                     Some
                                       FStar_Extraction_ML_Syntax.NoExtract
                                 | uu____1437 -> None) quals in
                          let flags' =
                            FStar_List.choose
                              (fun uu___157_1442  ->
                                 match uu___157_1442 with
                                 | {
                                     FStar_Syntax_Syntax.n =
                                       FStar_Syntax_Syntax.Tm_constant
                                       (FStar_Const.Const_string
                                       (data,uu____1447));
                                     FStar_Syntax_Syntax.tk = uu____1448;
                                     FStar_Syntax_Syntax.pos = uu____1449;
                                     FStar_Syntax_Syntax.vars = uu____1450;_}
                                     ->
                                     Some
                                       (FStar_Extraction_ML_Syntax.Attribute
                                          (FStar_Util.string_of_unicode data))
                                 | uu____1455 ->
                                     (FStar_Util.print_warning
                                        "Warning: unrecognized, non-string attribute, bother protz for a better error message";
                                      None)) attrs in
                          let uu____1459 =
                            let uu____1461 =
                              let uu____1462 =
                                FStar_Extraction_ML_Util.mlloc_of_range
                                  se.FStar_Syntax_Syntax.sigrng in
                              FStar_Extraction_ML_Syntax.MLM_Loc uu____1462 in
                            [uu____1461;
                            FStar_Extraction_ML_Syntax.MLM_Let
                              (flavor, (FStar_List.append flags flags'),
                                (FStar_List.rev ml_lbs'))] in
                          (g1, uu____1459))
                 | uu____1466 ->
                     let uu____1467 =
                       let uu____1468 =
                         FStar_Extraction_ML_Code.string_of_mlexpr
                           g.FStar_Extraction_ML_UEnv.currentModule ml_let in
                       FStar_Util.format1
                         "Impossible: Translated a let to a non-let: %s"
                         uu____1468 in
                     failwith uu____1467))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____1473,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____1477 =
             FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption) in
           if uu____1477
           then
             let always_fail =
               let imp =
                 let uu____1484 = FStar_Syntax_Util.arrow_formals t in
                 match uu____1484 with
                 | ([],t1) ->
                     let b =
                       let uu____1503 =
                         FStar_Syntax_Syntax.gen_bv "_" None t1 in
                       FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                         uu____1503 in
                     let uu____1504 = fail_exp lid t1 in
                     FStar_Syntax_Util.abs [b] uu____1504 None
                 | (bs,t1) ->
                     let uu____1522 = fail_exp lid t1 in
                     FStar_Syntax_Util.abs bs uu____1522 None in
               let uu___161_1528 = se in
               let uu____1529 =
                 let uu____1530 =
                   let uu____1536 =
                     let uu____1540 =
                       let uu____1542 =
                         let uu____1543 =
                           let uu____1546 =
                             FStar_Syntax_Syntax.lid_as_fv lid
                               FStar_Syntax_Syntax.Delta_constant None in
                           FStar_Util.Inr uu____1546 in
                         {
                           FStar_Syntax_Syntax.lbname = uu____1543;
                           FStar_Syntax_Syntax.lbunivs = [];
                           FStar_Syntax_Syntax.lbtyp = t;
                           FStar_Syntax_Syntax.lbeff =
                             FStar_Syntax_Const.effect_ML_lid;
                           FStar_Syntax_Syntax.lbdef = imp
                         } in
                       [uu____1542] in
                     (false, uu____1540) in
                   (uu____1536, [], []) in
                 FStar_Syntax_Syntax.Sig_let uu____1530 in
               {
                 FStar_Syntax_Syntax.sigel = uu____1529;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___161_1528.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___161_1528.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___161_1528.FStar_Syntax_Syntax.sigmeta)
               } in
             let uu____1553 = extract_sig g always_fail in
             (match uu____1553 with
              | (g1,mlm) ->
                  let uu____1564 =
                    FStar_Util.find_map quals
                      (fun uu___158_1566  ->
                         match uu___158_1566 with
                         | FStar_Syntax_Syntax.Discriminator l -> Some l
                         | uu____1569 -> None) in
                  (match uu____1564 with
                   | Some l ->
                       let uu____1574 =
                         let uu____1576 =
                           let uu____1577 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____1577 in
                         let uu____1578 =
                           let uu____1580 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l in
                           [uu____1580] in
                         uu____1576 :: uu____1578 in
                       (g1, uu____1574)
                   | uu____1582 ->
                       let uu____1584 =
                         FStar_Util.find_map quals
                           (fun uu___159_1586  ->
                              match uu___159_1586 with
                              | FStar_Syntax_Syntax.Projector (l,uu____1589)
                                  -> Some l
                              | uu____1590 -> None) in
                       (match uu____1584 with
                        | Some uu____1594 -> (g1, [])
                        | uu____1596 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____1602 = FStar_Extraction_ML_Term.term_as_mlexpr g e in
           (match uu____1602 with
            | (ml_main,uu____1610,uu____1611) ->
                let uu____1612 =
                  let uu____1614 =
                    let uu____1615 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____1615 in
                  [uu____1614; FStar_Extraction_ML_Syntax.MLM_Top ml_main] in
                (g, uu____1612))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____1617 ->
           failwith "impossible -- removed by tc.fs"
       | FStar_Syntax_Syntax.Sig_assume _
         |FStar_Syntax_Syntax.Sig_sub_effect _
          |FStar_Syntax_Syntax.Sig_effect_abbrev _ -> (g, [])
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (if p = FStar_Syntax_Syntax.LightOff
            then FStar_Options.set_ml_ish ()
            else ();
            (g, [])))
let extract_iface:
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.modul -> env_t =
  fun g  ->
    fun m  ->
      let uu____1635 =
        FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____1635 FStar_Pervasives.fst
let extract:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Extraction_ML_UEnv.env* FStar_Extraction_ML_Syntax.mllib
        Prims.list)
  =
  fun g  ->
    fun m  ->
      FStar_Syntax_Syntax.reset_gensym ();
      (let uu____1661 = FStar_Options.debug_any () in
       if uu____1661
       then
         let uu____1662 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
         FStar_Util.print1 "Extracting module %s\n" uu____1662
       else ());
      (let uu____1664 = FStar_Options.restore_cmd_line_options true in
       let name =
         FStar_Extraction_ML_Syntax.mlpath_of_lident
           m.FStar_Syntax_Syntax.name in
       let g1 =
         let uu___162_1667 = g in
         {
           FStar_Extraction_ML_UEnv.tcenv =
             (uu___162_1667.FStar_Extraction_ML_UEnv.tcenv);
           FStar_Extraction_ML_UEnv.gamma =
             (uu___162_1667.FStar_Extraction_ML_UEnv.gamma);
           FStar_Extraction_ML_UEnv.tydefs =
             (uu___162_1667.FStar_Extraction_ML_UEnv.tydefs);
           FStar_Extraction_ML_UEnv.currentModule = name
         } in
       let uu____1668 =
         FStar_Util.fold_map extract_sig g1
           m.FStar_Syntax_Syntax.declarations in
       match uu____1668 with
       | (g2,sigs) ->
           let mlm = FStar_List.flatten sigs in
           let is_kremlin =
             let uu____1685 = FStar_Options.codegen () in
             match uu____1685 with
             | Some "Kremlin" -> true
             | uu____1687 -> false in
           let uu____1689 =
             (((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
                (is_kremlin ||
                   (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)))
               &&
               (FStar_Options.should_extract
                  (m.FStar_Syntax_Syntax.name).FStar_Ident.str) in
           if uu____1689
           then
             ((let uu____1694 =
                 FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
               FStar_Util.print1 "Extracted module %s\n" uu____1694);
              (g2,
                [FStar_Extraction_ML_Syntax.MLLib
                   [(name, (Some ([], mlm)),
                      (FStar_Extraction_ML_Syntax.MLLib []))]]))
           else (g2, []))