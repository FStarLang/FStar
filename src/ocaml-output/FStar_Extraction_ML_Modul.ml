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
let binders_as_mlty_binders env bs =
  FStar_Util.fold_map
    (fun env1  ->
       fun uu____100  ->
         match uu____100 with
         | (bv,uu____108) ->
             let uu____109 =
               let uu____110 =
                 let uu____112 =
                   let uu____113 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv in
                   FStar_Extraction_ML_Syntax.MLTY_Var uu____113 in
                 Some uu____112 in
               FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____110 in
             let uu____114 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv in
             (uu____109, uu____114)) env bs
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
            let uu____142 =
              let uu____143 = FStar_Syntax_Subst.compress def in
              FStar_All.pipe_right uu____143 FStar_Syntax_Util.unmeta in
            FStar_All.pipe_right uu____142 FStar_Syntax_Util.un_uinst in
          let def2 =
            match def1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs uu____145 ->
                FStar_Extraction_ML_Term.normalize_abs def1
            | uu____160 -> def1 in
          let uu____161 =
            match def2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____168) ->
                FStar_Syntax_Subst.open_term bs body
            | uu____191 -> ([], def2) in
          match uu____161 with
          | (bs,body) ->
              let assumed =
                FStar_Util.for_some
                  (fun uu___149_203  ->
                     match uu___149_203 with
                     | FStar_Syntax_Syntax.Assumption  -> true
                     | uu____204 -> false) quals in
              let uu____205 = binders_as_mlty_binders env bs in
              (match uu____205 with
               | (env1,ml_bs) ->
                   let body1 =
                     let uu____223 =
                       FStar_Extraction_ML_Term.term_as_mlty env1 body in
                     FStar_All.pipe_right uu____223
                       (FStar_Extraction_ML_Util.eraseTypeDeep
                          (FStar_Extraction_ML_Util.udelta_unfold env1)) in
                   let mangled_projector =
                     let uu____226 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___150_228  ->
                               match uu___150_228 with
                               | FStar_Syntax_Syntax.Projector uu____229 ->
                                   true
                               | uu____232 -> false)) in
                     if uu____226
                     then
                       let mname = mangle_projector_lid lid in
                       Some ((mname.FStar_Ident.ident).FStar_Ident.idText)
                     else None in
                   let td =
                     let uu____248 =
                       let uu____259 = lident_as_mlsymbol lid in
                       (assumed, uu____259, mangled_projector, ml_bs,
                         (Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1))) in
                     [uu____248] in
                   let def3 =
                     let uu____287 =
                       let uu____288 =
                         FStar_Extraction_ML_Util.mlloc_of_range
                           (FStar_Ident.range_of_lid lid) in
                       FStar_Extraction_ML_Syntax.MLM_Loc uu____288 in
                     [uu____287; FStar_Extraction_ML_Syntax.MLM_Ty td] in
                   let env2 =
                     let uu____290 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___151_292  ->
                               match uu___151_292 with
                               | FStar_Syntax_Syntax.Assumption 
                                 |FStar_Syntax_Syntax.New  -> true
                               | uu____293 -> false)) in
                     if uu____290
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
    let uu____354 = FStar_Syntax_Print.lid_to_string i.iname in
    let uu____355 = FStar_Syntax_Print.binders_to_string " " i.iparams in
    let uu____356 = FStar_Syntax_Print.term_to_string i.ityp in
    let uu____357 =
      let uu____358 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let uu____363 = FStar_Syntax_Print.lid_to_string d.dname in
                let uu____364 =
                  let uu____365 = FStar_Syntax_Print.term_to_string d.dtyp in
                  Prims.strcat " : " uu____365 in
                Prims.strcat uu____363 uu____364)) in
      FStar_All.pipe_right uu____358 (FStar_String.concat "\n\t\t") in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____354 uu____355 uu____356
      uu____357
let bundle_as_inductive_families env ses quals =
  FStar_All.pipe_right ses
    (FStar_List.collect
       (fun se  ->
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,_us,bs,t,_mut_i,datas,quals1) ->
              let uu____406 = FStar_Syntax_Subst.open_term bs t in
              (match uu____406 with
               | (bs1,t1) ->
                   let datas1 =
                     FStar_All.pipe_right ses
                       (FStar_List.collect
                          (fun se1  ->
                             match se1.FStar_Syntax_Syntax.sigel with
                             | FStar_Syntax_Syntax.Sig_datacon
                                 (d,uu____419,t2,l',nparams,uu____423,uu____424)
                                 when FStar_Ident.lid_equals l l' ->
                                 let uu____429 =
                                   FStar_Syntax_Util.arrow_formals t2 in
                                 (match uu____429 with
                                  | (bs',body) ->
                                      let uu____450 =
                                        FStar_Util.first_N
                                          (FStar_List.length bs1) bs' in
                                      (match uu____450 with
                                       | (bs_params,rest) ->
                                           let subst1 =
                                             FStar_List.map2
                                               (fun uu____486  ->
                                                  fun uu____487  ->
                                                    match (uu____486,
                                                            uu____487)
                                                    with
                                                    | ((b',uu____497),
                                                       (b,uu____499)) ->
                                                        let uu____504 =
                                                          let uu____509 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              b in
                                                          (b', uu____509) in
                                                        FStar_Syntax_Syntax.NT
                                                          uu____504)
                                               bs_params bs1 in
                                           let t3 =
                                             let uu____511 =
                                               let uu____514 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   body in
                                               FStar_Syntax_Util.arrow rest
                                                 uu____514 in
                                             FStar_All.pipe_right uu____511
                                               (FStar_Syntax_Subst.subst
                                                  subst1) in
                                           [{ dname = d; dtyp = t3 }]))
                             | uu____519 -> [])) in
                   [{
                      iname = l;
                      iparams = bs1;
                      ityp = t1;
                      idatas = datas1;
                      iquals = quals1
                    }])
          | uu____520 -> []))
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
          let uu____557 =
            FStar_Extraction_ML_Term.term_as_mlty env1 ctor.dtyp in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env1) uu____557 in
        let tys = (ml_tyvars, mlt) in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp in
        let uu____568 =
          let uu____569 =
            FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false in
          Prims.fst uu____569 in
        let uu____572 =
          let uu____576 = lident_as_mlsymbol ctor.dname in
          let uu____577 = FStar_Extraction_ML_Util.argTypes mlt in
          (uu____576, uu____577) in
        (uu____568, uu____572) in
      let extract_one_family env1 ind =
        let uu____602 = binders_as_mlty_binders env1 ind.iparams in
        match uu____602 with
        | (env2,vars) ->
            let uu____628 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor vars) env2) in
            (match uu____628 with
             | (env3,ctors) ->
                 let uu____667 = FStar_Syntax_Util.arrow_formals ind.ityp in
                 (match uu____667 with
                  | (indices,uu____688) ->
                      let ml_params =
                        let uu____703 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____718  ->
                                    let uu____721 =
                                      let uu____722 =
                                        FStar_Util.string_of_int i in
                                      Prims.strcat "'dummyV" uu____722 in
                                    (uu____721, (Prims.parse_int "0")))) in
                        FStar_List.append vars uu____703 in
                      let tbody =
                        let uu____726 =
                          FStar_Util.find_opt
                            (fun uu___152_728  ->
                               match uu___152_728 with
                               | FStar_Syntax_Syntax.RecordType uu____729 ->
                                   true
                               | uu____734 -> false) ind.iquals in
                        match uu____726 with
                        | Some (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____741 = FStar_List.hd ctors in
                            (match uu____741 with
                             | (uu____748,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id  ->
                                        fun ty  ->
                                          let lid =
                                            FStar_Ident.lid_of_ids
                                              (FStar_List.append ns [id]) in
                                          let uu____762 =
                                            lident_as_mlsymbol lid in
                                          (uu____762, ty)) ids c_ty in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____763 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors in
                      let uu____765 =
                        let uu____776 = lident_as_mlsymbol ind.iname in
                        (false, uu____776, None, ml_params, (Some tbody)) in
                      (env3, uu____765))) in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               (l,uu____796,t,uu____798,uu____799,uu____800,uu____801);
             FStar_Syntax_Syntax.sigrng = uu____802;_}::[],(FStar_Syntax_Syntax.ExceptionConstructor
           )::[],uu____803)
          ->
          let uu____812 = extract_ctor [] env { dname = l; dtyp = t } in
          (match uu____812 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | FStar_Syntax_Syntax.Sig_bundle (ses,quals,uu____834) ->
          let ifams = bundle_as_inductive_families env ses quals in
          let uu____844 = FStar_Util.fold_map extract_one_family env ifams in
          (match uu____844 with
           | (env1,td) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Ty td]))
      | uu____896 -> failwith "Unexpected signature element"
let rec extract_sig:
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t* FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
  =
  fun g  ->
    fun se  ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u  ->
           let uu____914 = FStar_Syntax_Print.sigelt_to_string se in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____914);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle _
         |FStar_Syntax_Syntax.Sig_inductive_typ _
          |FStar_Syntax_Syntax.Sig_datacon _ -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers
             (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
           ->
           let extend_env g1 lid ml_name tm tysc =
             let uu____941 =
               let uu____944 =
                 FStar_Syntax_Syntax.lid_as_fv lid
                   FStar_Syntax_Syntax.Delta_equational None in
               FStar_Extraction_ML_UEnv.extend_fv' g1 uu____944 ml_name tysc
                 false false in
             match uu____941 with
             | (g2,mangled_name) ->
                 let uu____949 = mangled_name in
                 (match uu____949 with
                  | (n1,w) ->
                      ((let uu____955 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug
                               g2.FStar_Extraction_ML_UEnv.tcenv)
                            (FStar_Options.Other "ExtractionReify") in
                        if uu____955
                        then FStar_Util.print1 "Mangled name: %s\n" n1
                        else ());
                       (let lb =
                          {
                            FStar_Extraction_ML_Syntax.mllb_name =
                              mangled_name;
                            FStar_Extraction_ML_Syntax.mllb_tysc = None;
                            FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                            FStar_Extraction_ML_Syntax.mllb_def = tm;
                            FStar_Extraction_ML_Syntax.print_typ = false
                          } in
                        (g2,
                          (FStar_Extraction_ML_Syntax.MLM_Let
                             (FStar_Extraction_ML_Syntax.NonRec, [], [lb])))))) in
           let rec extract_fv tm =
             (let uu____967 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify") in
              if uu____967
              then
                let uu____968 = FStar_Syntax_Print.term_to_string tm in
                FStar_Util.print1 "extract_fv term: %s\n" uu____968
              else ());
             (let uu____970 =
                let uu____971 = FStar_Syntax_Subst.compress tm in
                uu____971.FStar_Syntax_Syntax.n in
              match uu____970 with
              | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____977) ->
                  extract_fv tm1
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let mlp =
                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  let uu____988 =
                    let uu____993 = FStar_Extraction_ML_UEnv.lookup_fv g fv in
                    FStar_All.pipe_left FStar_Util.right uu____993 in
                  (match uu____988 with
                   | (uu____1022,uu____1023,tysc,uu____1025) ->
                       let uu____1026 =
                         FStar_All.pipe_left
                           (FStar_Extraction_ML_Syntax.with_ty
                              FStar_Extraction_ML_Syntax.MLTY_Top)
                           (FStar_Extraction_ML_Syntax.MLE_Name mlp) in
                       (uu____1026, tysc))
              | uu____1027 -> failwith "Not an fv") in
           let extract_action g1 a =
             (let uu____1043 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g1.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify") in
              if uu____1043
              then
                let uu____1044 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_typ in
                let uu____1045 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_defn in
                FStar_Util.print2 "Action type %s and term %s\n" uu____1044
                  uu____1045
              else ());
             (let uu____1047 = FStar_Extraction_ML_UEnv.action_name ed a in
              match uu____1047 with
              | (a_nm,a_lid) ->
                  let lbname =
                    let uu____1057 =
                      FStar_Syntax_Syntax.new_bv
                        (Some
                           ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                        FStar_Syntax_Const.exp_unit in
                    FStar_Util.Inl uu____1057 in
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
                  let uu____1080 =
                    FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb in
                  (match uu____1080 with
                   | (a_let,uu____1087,ty) ->
                       let uu____1089 =
                         match a_let.FStar_Extraction_ML_Syntax.expr with
                         | FStar_Extraction_ML_Syntax.MLE_Let
                             ((uu____1094,uu____1095,mllb::[]),uu____1097) ->
                             (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                              with
                              | Some tysc ->
                                  ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                    tysc)
                              | None  -> failwith "No type scheme")
                         | uu____1108 -> failwith "Impossible" in
                       (match uu____1089 with
                        | (exp,tysc) ->
                            ((let uu____1116 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug
                                     g1.FStar_Extraction_ML_UEnv.tcenv)
                                  (FStar_Options.Other "ExtractionReify") in
                              if uu____1116
                              then
                                ((let uu____1118 =
                                    FStar_Extraction_ML_Code.string_of_mlty
                                      a_nm (Prims.snd tysc) in
                                  FStar_Util.print1 "Action typescheme: %s\n"
                                    uu____1118);
                                 FStar_List.iter
                                   (fun x  ->
                                      FStar_Util.print1
                                        "Action type binders: %s\n"
                                        (Prims.fst x)) (Prims.fst tysc))
                              else ());
                             extend_env g1 a_lid a_nm exp tysc)))) in
           let uu____1125 =
             let uu____1128 =
               FStar_Extraction_ML_UEnv.monad_op_name ed "return" in
             match uu____1128 with
             | (return_nm,return_lid) ->
                 let uu____1135 =
                   extract_fv (Prims.snd ed.FStar_Syntax_Syntax.return_repr) in
                 (match uu____1135 with
                  | (return_tm,ty_sc) ->
                      extend_env g return_lid return_nm return_tm ty_sc) in
           (match uu____1125 with
            | (g1,return_decl) ->
                let uu____1148 =
                  let uu____1151 =
                    FStar_Extraction_ML_UEnv.monad_op_name ed "bind" in
                  match uu____1151 with
                  | (bind_nm,bind_lid) ->
                      let uu____1158 =
                        extract_fv
                          (Prims.snd ed.FStar_Syntax_Syntax.bind_repr) in
                      (match uu____1158 with
                       | (bind_tm,ty_sc) ->
                           extend_env g1 bind_lid bind_nm bind_tm ty_sc) in
                (match uu____1148 with
                 | (g2,bind_decl) ->
                     let uu____1171 =
                       FStar_Util.fold_map extract_action g2
                         ed.FStar_Syntax_Syntax.actions in
                     (match uu____1171 with
                      | (g3,actions) ->
                          (g3,
                            (FStar_List.append [return_decl; bind_decl]
                               actions)))))
       | FStar_Syntax_Syntax.Sig_new_effect uu____1183 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____1186,t,quals) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let uu____1191 =
             let uu____1192 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___153_1194  ->
                       match uu___153_1194 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____1195 -> false)) in
             FStar_All.pipe_right uu____1192 Prims.op_Negation in
           if uu____1191
           then (g, [])
           else
             (let uu____1201 = FStar_Syntax_Util.arrow_formals t in
              match uu____1201 with
              | (bs,uu____1213) ->
                  let fv =
                    FStar_Syntax_Syntax.lid_as_fv lid
                      FStar_Syntax_Syntax.Delta_constant None in
                  let uu____1225 =
                    FStar_Syntax_Util.abs bs FStar_TypeChecker_Common.t_unit
                      None in
                  extract_typ_abbrev g fv quals uu____1225)
       | FStar_Syntax_Syntax.Sig_let
           ((false ,lb::[]),uu____1232,quals,uu____1234) when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let uu____1245 = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
           extract_typ_abbrev g uu____1245 quals lb.FStar_Syntax_Syntax.lbdef
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____1247,quals,attrs) ->
           let elet =
             (FStar_Syntax_Syntax.mk
                (FStar_Syntax_Syntax.Tm_let
                   (lbs, FStar_Syntax_Const.exp_false_bool))) None
               se.FStar_Syntax_Syntax.sigrng in
           let uu____1267 = FStar_Extraction_ML_Term.term_as_mlexpr g elet in
           (match uu____1267 with
            | (ml_let,uu____1275,uu____1276) ->
                (match ml_let.FStar_Extraction_ML_Syntax.expr with
                 | FStar_Extraction_ML_Syntax.MLE_Let
                     ((flavor,uu____1281,bindings),uu____1283) ->
                     let uu____1290 =
                       FStar_List.fold_left2
                         (fun uu____1297  ->
                            fun ml_lb  ->
                              fun uu____1299  ->
                                match (uu____1297, uu____1299) with
                                | ((env,ml_lbs),{
                                                  FStar_Syntax_Syntax.lbname
                                                    = lbname;
                                                  FStar_Syntax_Syntax.lbunivs
                                                    = uu____1312;
                                                  FStar_Syntax_Syntax.lbtyp =
                                                    t;
                                                  FStar_Syntax_Syntax.lbeff =
                                                    uu____1314;
                                                  FStar_Syntax_Syntax.lbdef =
                                                    uu____1315;_})
                                    ->
                                    let lb_lid =
                                      let uu____1329 =
                                        let uu____1334 =
                                          FStar_Util.right lbname in
                                        uu____1334.FStar_Syntax_Syntax.fv_name in
                                      uu____1329.FStar_Syntax_Syntax.v in
                                    let uu____1338 =
                                      let uu____1341 =
                                        FStar_All.pipe_right quals
                                          (FStar_Util.for_some
                                             (fun uu___154_1343  ->
                                                match uu___154_1343 with
                                                | FStar_Syntax_Syntax.Projector
                                                    uu____1344 -> true
                                                | uu____1347 -> false)) in
                                      if uu____1341
                                      then
                                        let mname =
                                          let uu____1351 =
                                            mangle_projector_lid lb_lid in
                                          FStar_All.pipe_right uu____1351
                                            FStar_Extraction_ML_Syntax.mlpath_of_lident in
                                        let uu____1352 =
                                          let uu____1355 =
                                            FStar_Util.right lbname in
                                          let uu____1356 =
                                            FStar_Util.must
                                              ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc in
                                          FStar_Extraction_ML_UEnv.extend_fv'
                                            env uu____1355 mname uu____1356
                                            ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                            false in
                                        match uu____1352 with
                                        | (env1,uu____1360) ->
                                            (env1,
                                              (let uu___159_1361 = ml_lb in
                                               {
                                                 FStar_Extraction_ML_Syntax.mllb_name
                                                   =
                                                   ((Prims.snd mname),
                                                     (Prims.parse_int "0"));
                                                 FStar_Extraction_ML_Syntax.mllb_tysc
                                                   =
                                                   (uu___159_1361.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                 FStar_Extraction_ML_Syntax.mllb_add_unit
                                                   =
                                                   (uu___159_1361.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                 FStar_Extraction_ML_Syntax.mllb_def
                                                   =
                                                   (uu___159_1361.FStar_Extraction_ML_Syntax.mllb_def);
                                                 FStar_Extraction_ML_Syntax.print_typ
                                                   =
                                                   (uu___159_1361.FStar_Extraction_ML_Syntax.print_typ)
                                               }))
                                      else
                                        (let uu____1364 =
                                           let uu____1365 =
                                             let uu____1368 =
                                               FStar_Util.must
                                                 ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc in
                                             FStar_Extraction_ML_UEnv.extend_lb
                                               env lbname t uu____1368
                                               ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                               false in
                                           FStar_All.pipe_left Prims.fst
                                             uu____1365 in
                                         (uu____1364, ml_lb)) in
                                    (match uu____1338 with
                                     | (g1,ml_lb1) ->
                                         (g1, (ml_lb1 :: ml_lbs)))) (g, [])
                         bindings (Prims.snd lbs) in
                     (match uu____1290 with
                      | (g1,ml_lbs') ->
                          let flags =
                            FStar_List.choose
                              (fun uu___155_1388  ->
                                 match uu___155_1388 with
                                 | FStar_Syntax_Syntax.Assumption  ->
                                     Some FStar_Extraction_ML_Syntax.Assumed
                                 | FStar_Syntax_Syntax.Private  ->
                                     Some FStar_Extraction_ML_Syntax.Private
                                 | FStar_Syntax_Syntax.NoExtract  ->
                                     Some
                                       FStar_Extraction_ML_Syntax.NoExtract
                                 | uu____1390 -> None) quals in
                          let flags' =
                            FStar_List.choose
                              (fun uu___156_1395  ->
                                 match uu___156_1395 with
                                 | {
                                     FStar_Syntax_Syntax.n =
                                       FStar_Syntax_Syntax.Tm_constant
                                       (FStar_Const.Const_string
                                       (data,uu____1400));
                                     FStar_Syntax_Syntax.tk = uu____1401;
                                     FStar_Syntax_Syntax.pos = uu____1402;
                                     FStar_Syntax_Syntax.vars = uu____1403;_}
                                     ->
                                     Some
                                       (FStar_Extraction_ML_Syntax.Attribute
                                          (FStar_Util.string_of_unicode data))
                                 | uu____1408 ->
                                     (FStar_Util.print_warning
                                        "Warning: unrecognized, non-string attribute, bother protz for a better error message";
                                      None)) attrs in
                          let uu____1412 =
                            let uu____1414 =
                              let uu____1415 =
                                FStar_Extraction_ML_Util.mlloc_of_range
                                  se.FStar_Syntax_Syntax.sigrng in
                              FStar_Extraction_ML_Syntax.MLM_Loc uu____1415 in
                            [uu____1414;
                            FStar_Extraction_ML_Syntax.MLM_Let
                              (flavor, (FStar_List.append flags flags'),
                                (FStar_List.rev ml_lbs'))] in
                          (g1, uu____1412))
                 | uu____1419 ->
                     let uu____1420 =
                       let uu____1421 =
                         FStar_Extraction_ML_Code.string_of_mlexpr
                           g.FStar_Extraction_ML_UEnv.currentModule ml_let in
                       FStar_Util.format1
                         "Impossible: Translated a let to a non-let: %s"
                         uu____1421 in
                     failwith uu____1420))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____1426,t,quals) ->
           let uu____1431 =
             FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption) in
           if uu____1431
           then
             let always_fail =
               let imp =
                 let uu____1438 = FStar_Syntax_Util.arrow_formals t in
                 match uu____1438 with
                 | ([],t1) ->
                     let b =
                       let uu____1457 =
                         FStar_Syntax_Syntax.gen_bv "_" None t1 in
                       FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                         uu____1457 in
                     let uu____1458 = fail_exp lid t1 in
                     FStar_Syntax_Util.abs [b] uu____1458 None
                 | (bs,t1) ->
                     let uu____1476 = fail_exp lid t1 in
                     FStar_Syntax_Util.abs bs uu____1476 None in
               let uu___160_1482 = se in
               let uu____1483 =
                 let uu____1484 =
                   let uu____1492 =
                     let uu____1496 =
                       let uu____1498 =
                         let uu____1499 =
                           let uu____1502 =
                             FStar_Syntax_Syntax.lid_as_fv lid
                               FStar_Syntax_Syntax.Delta_constant None in
                           FStar_Util.Inr uu____1502 in
                         {
                           FStar_Syntax_Syntax.lbname = uu____1499;
                           FStar_Syntax_Syntax.lbunivs = [];
                           FStar_Syntax_Syntax.lbtyp = t;
                           FStar_Syntax_Syntax.lbeff =
                             FStar_Syntax_Const.effect_ML_lid;
                           FStar_Syntax_Syntax.lbdef = imp
                         } in
                       [uu____1498] in
                     (false, uu____1496) in
                   (uu____1492, [], quals, []) in
                 FStar_Syntax_Syntax.Sig_let uu____1484 in
               {
                 FStar_Syntax_Syntax.sigel = uu____1483;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___160_1482.FStar_Syntax_Syntax.sigrng)
               } in
             let uu____1510 = extract_sig g always_fail in
             (match uu____1510 with
              | (g1,mlm) ->
                  let uu____1521 =
                    FStar_Util.find_map quals
                      (fun uu___157_1523  ->
                         match uu___157_1523 with
                         | FStar_Syntax_Syntax.Discriminator l -> Some l
                         | uu____1526 -> None) in
                  (match uu____1521 with
                   | Some l ->
                       let uu____1531 =
                         let uu____1533 =
                           let uu____1534 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____1534 in
                         let uu____1535 =
                           let uu____1537 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l in
                           [uu____1537] in
                         uu____1533 :: uu____1535 in
                       (g1, uu____1531)
                   | uu____1539 ->
                       let uu____1541 =
                         FStar_Util.find_map quals
                           (fun uu___158_1543  ->
                              match uu___158_1543 with
                              | FStar_Syntax_Syntax.Projector (l,uu____1546)
                                  -> Some l
                              | uu____1547 -> None) in
                       (match uu____1541 with
                        | Some uu____1551 -> (g1, [])
                        | uu____1553 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____1559 = FStar_Extraction_ML_Term.term_as_mlexpr g e in
           (match uu____1559 with
            | (ml_main,uu____1567,uu____1568) ->
                let uu____1569 =
                  let uu____1571 =
                    let uu____1572 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____1572 in
                  [uu____1571; FStar_Extraction_ML_Syntax.MLM_Top ml_main] in
                (g, uu____1569))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____1574 ->
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
      let uu____1592 =
        FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____1592 Prims.fst
let extract:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Extraction_ML_UEnv.env* FStar_Extraction_ML_Syntax.mllib
        Prims.list)
  =
  fun g  ->
    fun m  ->
      FStar_Syntax_Syntax.reset_gensym ();
      (let uu____1617 = FStar_Options.restore_cmd_line_options true in
       let name =
         FStar_Extraction_ML_Syntax.mlpath_of_lident
           m.FStar_Syntax_Syntax.name in
       let g1 =
         let uu___161_1620 = g in
         {
           FStar_Extraction_ML_UEnv.tcenv =
             (uu___161_1620.FStar_Extraction_ML_UEnv.tcenv);
           FStar_Extraction_ML_UEnv.gamma =
             (uu___161_1620.FStar_Extraction_ML_UEnv.gamma);
           FStar_Extraction_ML_UEnv.tydefs =
             (uu___161_1620.FStar_Extraction_ML_UEnv.tydefs);
           FStar_Extraction_ML_UEnv.currentModule = name
         } in
       let uu____1621 =
         FStar_Util.fold_map extract_sig g1
           m.FStar_Syntax_Syntax.declarations in
       match uu____1621 with
       | (g2,sigs) ->
           let mlm = FStar_List.flatten sigs in
           let is_kremlin =
             let uu____1638 = FStar_Options.codegen () in
             match uu____1638 with
             | Some "Kremlin" -> true
             | uu____1640 -> false in
           let uu____1642 =
             (((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
                (is_kremlin ||
                   (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)))
               &&
               (FStar_Options.should_extract
                  (m.FStar_Syntax_Syntax.name).FStar_Ident.str) in
           if uu____1642
           then
             ((let uu____1647 =
                 FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
               FStar_Util.print1 "Extracted module %s\n" uu____1647);
              (g2,
                [FStar_Extraction_ML_Syntax.MLLib
                   [(name, (Some ([], mlm)),
                      (FStar_Extraction_ML_Syntax.MLLib []))]]))
           else (g2, []))