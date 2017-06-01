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
let as_pair uu___152_88 =
  match uu___152_88 with
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
                  (fun uu___153_234  ->
                     match uu___153_234 with
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
                            (fun uu___154_259  ->
                               match uu___154_259 with
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
                            (fun uu___155_323  ->
                               match uu___155_323 with
                               | FStar_Syntax_Syntax.Assumption 
                                 |FStar_Syntax_Syntax.New  -> true
                               | uu____324 -> false)) in
                     if uu____321
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
    let uu____393 = FStar_Syntax_Print.lid_to_string i.iname in
    let uu____394 = FStar_Syntax_Print.binders_to_string " " i.iparams in
    let uu____395 = FStar_Syntax_Print.term_to_string i.ityp in
    let uu____396 =
      let uu____397 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let uu____402 = FStar_Syntax_Print.lid_to_string d.dname in
                let uu____403 =
                  let uu____404 = FStar_Syntax_Print.term_to_string d.dtyp in
                  Prims.strcat " : " uu____404 in
                Prims.strcat uu____402 uu____403)) in
      FStar_All.pipe_right uu____397 (FStar_String.concat "\n\t\t") in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____393 uu____394 uu____395
      uu____396
let bundle_as_inductive_families env ses quals =
  FStar_All.pipe_right ses
    (FStar_List.collect
       (fun se  ->
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_inductive_typ (l,_us,bs,t,_mut_i,datas)
              ->
              let uu____447 = FStar_Syntax_Subst.open_term bs t in
              (match uu____447 with
               | (bs1,t1) ->
                   let datas1 =
                     FStar_All.pipe_right ses
                       (FStar_List.collect
                          (fun se1  ->
                             match se1.FStar_Syntax_Syntax.sigel with
                             | FStar_Syntax_Syntax.Sig_datacon
                                 (d,uu____460,t2,l',nparams,uu____464) when
                                 FStar_Ident.lid_equals l l' ->
                                 let uu____467 =
                                   FStar_Syntax_Util.arrow_formals t2 in
                                 (match uu____467 with
                                  | (bs',body) ->
                                      let uu____488 =
                                        FStar_Util.first_N
                                          (FStar_List.length bs1) bs' in
                                      (match uu____488 with
                                       | (bs_params,rest) ->
                                           let subst1 =
                                             FStar_List.map2
                                               (fun uu____524  ->
                                                  fun uu____525  ->
                                                    match (uu____524,
                                                            uu____525)
                                                    with
                                                    | ((b',uu____535),
                                                       (b,uu____537)) ->
                                                        let uu____542 =
                                                          let uu____547 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              b in
                                                          (b', uu____547) in
                                                        FStar_Syntax_Syntax.NT
                                                          uu____542)
                                               bs_params bs1 in
                                           let t3 =
                                             let uu____549 =
                                               let uu____552 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   body in
                                               FStar_Syntax_Util.arrow rest
                                                 uu____552 in
                                             FStar_All.pipe_right uu____549
                                               (FStar_Syntax_Subst.subst
                                                  subst1) in
                                           [{ dname = d; dtyp = t3 }]))
                             | uu____557 -> [])) in
                   [{
                      iname = l;
                      iparams = bs1;
                      ityp = t1;
                      idatas = datas1;
                      iquals = (se.FStar_Syntax_Syntax.sigquals)
                    }])
          | uu____558 -> []))
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
          let uu____597 =
            FStar_Extraction_ML_Term.term_as_mlty env1 ctor.dtyp in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env1) uu____597 in
        let tys = (ml_tyvars, mlt) in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp in
        let uu____608 =
          let uu____609 =
            FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false in
          Prims.fst uu____609 in
        let uu____612 =
          let uu____616 = lident_as_mlsymbol ctor.dname in
          let uu____617 = FStar_Extraction_ML_Util.argTypes mlt in
          (uu____616, uu____617) in
        (uu____608, uu____612) in
      let extract_one_family env1 ind =
        let uu____642 = binders_as_mlty_binders env1 ind.iparams in
        match uu____642 with
        | (env2,vars) ->
            let uu____668 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor vars) env2) in
            (match uu____668 with
             | (env3,ctors) ->
                 let uu____707 = FStar_Syntax_Util.arrow_formals ind.ityp in
                 (match uu____707 with
                  | (indices,uu____728) ->
                      let ml_params =
                        let uu____743 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____758  ->
                                    let uu____761 =
                                      let uu____762 =
                                        FStar_Util.string_of_int i in
                                      Prims.strcat "'dummyV" uu____762 in
                                    (uu____761, (Prims.parse_int "0")))) in
                        FStar_List.append vars uu____743 in
                      let tbody =
                        let uu____766 =
                          FStar_Util.find_opt
                            (fun uu___156_768  ->
                               match uu___156_768 with
                               | FStar_Syntax_Syntax.RecordType uu____769 ->
                                   true
                               | uu____774 -> false) ind.iquals in
                        match uu____766 with
                        | Some (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____781 = FStar_List.hd ctors in
                            (match uu____781 with
                             | (uu____788,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id  ->
                                        fun ty  ->
                                          let lid =
                                            FStar_Ident.lid_of_ids
                                              (FStar_List.append ns [id]) in
                                          let uu____802 =
                                            lident_as_mlsymbol lid in
                                          (uu____802, ty)) ids c_ty in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____803 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors in
                      let uu____805 =
                        let uu____816 = lident_as_mlsymbol ind.iname in
                        (false, uu____816, None, ml_params, (Some tbody)) in
                      (env3, uu____805))) in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____837,t,uu____839,uu____840,uu____841);
            FStar_Syntax_Syntax.sigrng = uu____842;
            FStar_Syntax_Syntax.sigquals = uu____843;
            FStar_Syntax_Syntax.sigmeta = uu____844;_}::[],uu____845),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____853 = extract_ctor [] env { dname = l; dtyp = t } in
          (match uu____853 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____874),quals) ->
          let ifams = bundle_as_inductive_families env ses quals in
          let uu____885 = FStar_Util.fold_map extract_one_family env ifams in
          (match uu____885 with
           | (env1,td) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Ty td]))
      | uu____937 -> failwith "Unexpected signature element"
let rec extract_sig:
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t* FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
  =
  fun g  ->
    fun se  ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u  ->
           let uu____960 = FStar_Syntax_Print.sigelt_to_string se in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____960);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle _
         |FStar_Syntax_Syntax.Sig_inductive_typ _
          |FStar_Syntax_Syntax.Sig_datacon _ -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
           ->
           let extend_env g1 lid ml_name tm tysc =
             let uu____987 =
               let uu____990 =
                 FStar_Syntax_Syntax.lid_as_fv lid
                   FStar_Syntax_Syntax.Delta_equational None in
               FStar_Extraction_ML_UEnv.extend_fv' g1 uu____990 ml_name tysc
                 false false in
             match uu____987 with
             | (g2,mangled_name) ->
                 ((let uu____996 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          g2.FStar_Extraction_ML_UEnv.tcenv)
                       (FStar_Options.Other "ExtractionReify") in
                   if uu____996
                   then
                     FStar_Util.print1 "Mangled name: %s\n"
                       (Prims.fst mangled_name)
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
             (let uu____1008 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify") in
              if uu____1008
              then
                let uu____1009 = FStar_Syntax_Print.term_to_string tm in
                FStar_Util.print1 "extract_fv term: %s\n" uu____1009
              else ());
             (let uu____1011 =
                let uu____1012 = FStar_Syntax_Subst.compress tm in
                uu____1012.FStar_Syntax_Syntax.n in
              match uu____1011 with
              | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____1018) ->
                  extract_fv tm1
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let mlp =
                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  let uu____1029 =
                    let uu____1034 = FStar_Extraction_ML_UEnv.lookup_fv g fv in
                    FStar_All.pipe_left FStar_Util.right uu____1034 in
                  (match uu____1029 with
                   | (uu____1063,uu____1064,tysc,uu____1066) ->
                       let uu____1067 =
                         FStar_All.pipe_left
                           (FStar_Extraction_ML_Syntax.with_ty
                              FStar_Extraction_ML_Syntax.MLTY_Top)
                           (FStar_Extraction_ML_Syntax.MLE_Name mlp) in
                       (uu____1067, tysc))
              | uu____1068 -> failwith "Not an fv") in
           let extract_action g1 a =
             (let uu____1084 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g1.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify") in
              if uu____1084
              then
                let uu____1085 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_typ in
                let uu____1086 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_defn in
                FStar_Util.print2 "Action type %s and term %s\n" uu____1085
                  uu____1086
              else ());
             (let uu____1088 = FStar_Extraction_ML_UEnv.action_name ed a in
              match uu____1088 with
              | (a_nm,a_lid) ->
                  let lbname =
                    let uu____1098 =
                      FStar_Syntax_Syntax.new_bv
                        (Some
                           ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                        FStar_Syntax_Syntax.tun in
                    FStar_Util.Inl uu____1098 in
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
                  let uu____1121 =
                    FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb in
                  (match uu____1121 with
                   | (a_let,uu____1128,ty) ->
                       ((let uu____1131 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug
                                g1.FStar_Extraction_ML_UEnv.tcenv)
                             (FStar_Options.Other "ExtractionReify") in
                         if uu____1131
                         then
                           let uu____1132 =
                             FStar_Extraction_ML_Code.string_of_mlexpr a_nm
                               a_let in
                           FStar_Util.print1 "Extracted action term: %s\n"
                             uu____1132
                         else ());
                        (let uu____1134 =
                           match a_let.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_Let
                               ((uu____1139,uu____1140,mllb::[]),uu____1142)
                               ->
                               (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                                with
                                | Some tysc ->
                                    ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                      tysc)
                                | None  -> failwith "No type scheme")
                           | uu____1153 -> failwith "Impossible" in
                         match uu____1134 with
                         | (exp,tysc) ->
                             ((let uu____1161 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug
                                      g1.FStar_Extraction_ML_UEnv.tcenv)
                                   (FStar_Options.Other "ExtractionReify") in
                               if uu____1161
                               then
                                 ((let uu____1163 =
                                     FStar_Extraction_ML_Code.string_of_mlty
                                       a_nm (Prims.snd tysc) in
                                   FStar_Util.print1
                                     "Extracted action type: %s\n" uu____1163);
                                  FStar_List.iter
                                    (fun x  ->
                                       FStar_Util.print1 "and binders: %s\n"
                                         (Prims.fst x)) (Prims.fst tysc))
                               else ());
                              extend_env g1 a_lid a_nm exp tysc))))) in
           let uu____1170 =
             let uu____1173 =
               extract_fv (Prims.snd ed.FStar_Syntax_Syntax.return_repr) in
             match uu____1173 with
             | (return_tm,ty_sc) ->
                 let uu____1181 =
                   FStar_Extraction_ML_UEnv.monad_op_name ed "return" in
                 (match uu____1181 with
                  | (return_nm,return_lid) ->
                      extend_env g return_lid return_nm return_tm ty_sc) in
           (match uu____1170 with
            | (g1,return_decl) ->
                let uu____1193 =
                  let uu____1196 =
                    extract_fv (Prims.snd ed.FStar_Syntax_Syntax.bind_repr) in
                  match uu____1196 with
                  | (bind_tm,ty_sc) ->
                      let uu____1204 =
                        FStar_Extraction_ML_UEnv.monad_op_name ed "bind" in
                      (match uu____1204 with
                       | (bind_nm,bind_lid) ->
                           extend_env g1 bind_lid bind_nm bind_tm ty_sc) in
                (match uu____1193 with
                 | (g2,bind_decl) ->
                     let uu____1216 =
                       FStar_Util.fold_map extract_action g2
                         ed.FStar_Syntax_Syntax.actions in
                     (match uu____1216 with
                      | (g3,actions) ->
                          (g3,
                            (FStar_List.append [return_decl; bind_decl]
                               actions)))))
       | FStar_Syntax_Syntax.Sig_new_effect uu____1228 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____1231,t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____1235 =
             let uu____1236 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___157_1238  ->
                       match uu___157_1238 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____1239 -> false)) in
             Prims.op_Negation uu____1236 in
           if uu____1235
           then (g, [])
           else
             (let uu____1245 = FStar_Syntax_Util.arrow_formals t in
              match uu____1245 with
              | (bs,uu____1257) ->
                  let fv =
                    FStar_Syntax_Syntax.lid_as_fv lid
                      FStar_Syntax_Syntax.Delta_constant None in
                  let uu____1269 =
                    FStar_Syntax_Util.abs bs FStar_TypeChecker_Common.t_unit
                      None in
                  extract_typ_abbrev g fv quals uu____1269)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____1276,uu____1277)
           when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____1288 =
             let uu____1293 =
               FStar_TypeChecker_Env.open_universes_in
                 g.FStar_Extraction_ML_UEnv.tcenv
                 lb.FStar_Syntax_Syntax.lbunivs
                 [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp] in
             match uu____1293 with
             | (tcenv,uu____1309,def_typ) ->
                 let uu____1313 = as_pair def_typ in (tcenv, uu____1313) in
           (match uu____1288 with
            | (tcenv,(lbdef,lbtyp)) ->
                let lbtyp1 =
                  FStar_TypeChecker_Normalize.unfold_whnf tcenv lbtyp in
                let lbdef1 =
                  FStar_TypeChecker_Normalize.eta_expand_with_type tcenv
                    lbdef lbtyp1 in
                let uu____1328 =
                  FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                extract_typ_abbrev g uu____1328 quals lbdef1)
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____1330,attrs) ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let elet =
             (FStar_Syntax_Syntax.mk
                (FStar_Syntax_Syntax.Tm_let
                   (lbs, FStar_Syntax_Const.exp_false_bool))) None
               se.FStar_Syntax_Syntax.sigrng in
           let tactic_registration_decl =
             let is_tactic_decl tac_lid h =
               match h.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_uinst (h',uu____1359) ->
                   let uu____1364 =
                     let uu____1365 = FStar_Syntax_Subst.compress h' in
                     uu____1365.FStar_Syntax_Syntax.n in
                   (match uu____1364 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Syntax_Const.tactic_lid
                        ->
                        let uu____1369 =
                          let uu____1370 =
                            FStar_Extraction_ML_Syntax.string_of_mlpath
                              g.FStar_Extraction_ML_UEnv.currentModule in
                          uu____1370 = "FStar.Tactics" in
                        Prims.op_Negation uu____1369
                    | uu____1371 -> false)
               | uu____1372 -> false in
             let mk_interpretation_fun uu____1376 =
               FStar_Extraction_ML_Syntax.MLE_Const
                 FStar_Extraction_ML_Syntax.MLC_Unit in
             let mk_registration lid t bs =
               let h =
                 let uu____1398 =
                   let uu____1399 =
                     let uu____1400 =
                       FStar_Syntax_Const.fstar_tactics_lid
                         "Native.register_tactic" in
                     FStar_Extraction_ML_Syntax.mlpath_of_lident uu____1400 in
                   FStar_Extraction_ML_Syntax.MLE_Name uu____1399 in
                 FStar_All.pipe_left
                   (FStar_Extraction_ML_Syntax.with_ty
                      FStar_Extraction_ML_Syntax.MLTY_Top) uu____1398 in
               let lid_arg =
                 let uu____1402 =
                   let uu____1403 = FStar_Ident.string_of_lid lid in
                   FStar_Extraction_ML_Syntax.MLC_String uu____1403 in
                 FStar_Extraction_ML_Syntax.MLE_Const uu____1402 in
               let arity =
                 let uu____1405 =
                   let uu____1406 =
                     let uu____1412 =
                       FStar_Util.string_of_int (FStar_List.length bs) in
                     (uu____1412, None) in
                   FStar_Extraction_ML_Syntax.MLC_Int uu____1406 in
                 FStar_Extraction_ML_Syntax.MLE_Const uu____1405 in
               let interp = mk_interpretation_fun () in
               let app =
                 let uu____1425 =
                   let uu____1426 =
                     let uu____1430 =
                       FStar_List.map
                         (FStar_Extraction_ML_Syntax.with_ty
                            FStar_Extraction_ML_Syntax.MLTY_Top)
                         [lid_arg; arity; interp] in
                     (h, uu____1430) in
                   FStar_Extraction_ML_Syntax.MLE_App uu____1426 in
                 FStar_All.pipe_left
                   (FStar_Extraction_ML_Syntax.with_ty
                      FStar_Extraction_ML_Syntax.MLTY_Top) uu____1425 in
               FStar_Extraction_ML_Syntax.MLM_Top app in
             match Prims.snd lbs with
             | hd1::[] ->
                 let uu____1436 =
                   FStar_Syntax_Util.arrow_formals_comp
                     hd1.FStar_Syntax_Syntax.lbtyp in
                 (match uu____1436 with
                  | (bs,comp) ->
                      let t = FStar_Syntax_Util.comp_result comp in
                      let uu____1454 =
                        let uu____1455 = FStar_Syntax_Subst.compress t in
                        uu____1455.FStar_Syntax_Syntax.n in
                      (match uu____1454 with
                       | FStar_Syntax_Syntax.Tm_app (h,args) ->
                           let h1 = FStar_Syntax_Subst.compress h in
                           let tac_lid =
                             let uu____1477 =
                               let uu____1482 =
                                 FStar_Util.right
                                   hd1.FStar_Syntax_Syntax.lbname in
                               uu____1482.FStar_Syntax_Syntax.fv_name in
                             uu____1477.FStar_Syntax_Syntax.v in
                           let assm_lid =
                             let uu____1487 =
                               FStar_All.pipe_left FStar_Ident.id_of_text
                                 (Prims.strcat "__"
                                    (tac_lid.FStar_Ident.ident).FStar_Ident.idText) in
                             FStar_Ident.lid_of_ns_and_id
                               tac_lid.FStar_Ident.ns uu____1487 in
                           let uu____1488 = is_tactic_decl assm_lid h1 in
                           if uu____1488
                           then
                             ((let uu____1491 =
                                 FStar_Syntax_Print.term_to_string h1 in
                               FStar_Util.print1 "Head %s \n" uu____1491);
                              (let uu____1493 =
                                 let uu____1494 =
                                   let uu____1495 = FStar_List.hd args in
                                   Prims.fst uu____1495 in
                                 FStar_Syntax_Print.term_to_string uu____1494 in
                               FStar_Util.print1 "Arg %s \n" uu____1493);
                              (let uu____1507 =
                                 FStar_Syntax_Print.term_to_string
                                   hd1.FStar_Syntax_Syntax.lbtyp in
                               FStar_Util.print1 "Type: %s\n" uu____1507);
                              FStar_List.iter
                                (fun x  ->
                                   let uu____1514 =
                                     FStar_Syntax_Print.term_to_string
                                       (Prims.fst x).FStar_Syntax_Syntax.sort in
                                   FStar_Util.print1 "Binder %s\n" uu____1514)
                                bs;
                              (let uu____1515 =
                                 mk_registration assm_lid
                                   hd1.FStar_Syntax_Syntax.lbtyp bs in
                               [uu____1515]))
                           else []
                       | uu____1517 -> []))
             | uu____1518 -> [] in
           let uu____1520 = FStar_Extraction_ML_Term.term_as_mlexpr g elet in
           (match uu____1520 with
            | (ml_let,uu____1528,uu____1529) ->
                (match ml_let.FStar_Extraction_ML_Syntax.expr with
                 | FStar_Extraction_ML_Syntax.MLE_Let
                     ((flavor,uu____1534,bindings),uu____1536) ->
                     let uu____1543 =
                       FStar_List.fold_left2
                         (fun uu____1550  ->
                            fun ml_lb  ->
                              fun uu____1552  ->
                                match (uu____1550, uu____1552) with
                                | ((env,ml_lbs),{
                                                  FStar_Syntax_Syntax.lbname
                                                    = lbname;
                                                  FStar_Syntax_Syntax.lbunivs
                                                    = uu____1565;
                                                  FStar_Syntax_Syntax.lbtyp =
                                                    t;
                                                  FStar_Syntax_Syntax.lbeff =
                                                    uu____1567;
                                                  FStar_Syntax_Syntax.lbdef =
                                                    uu____1568;_})
                                    ->
                                    let lb_lid =
                                      let uu____1582 =
                                        let uu____1587 =
                                          FStar_Util.right lbname in
                                        uu____1587.FStar_Syntax_Syntax.fv_name in
                                      uu____1582.FStar_Syntax_Syntax.v in
                                    let uu____1591 =
                                      let uu____1594 =
                                        FStar_All.pipe_right quals
                                          (FStar_Util.for_some
                                             (fun uu___158_1596  ->
                                                match uu___158_1596 with
                                                | FStar_Syntax_Syntax.Projector
                                                    uu____1597 -> true
                                                | uu____1600 -> false)) in
                                      if uu____1594
                                      then
                                        let mname =
                                          let uu____1604 =
                                            mangle_projector_lid lb_lid in
                                          FStar_All.pipe_right uu____1604
                                            FStar_Extraction_ML_Syntax.mlpath_of_lident in
                                        let uu____1605 =
                                          let uu____1608 =
                                            FStar_Util.right lbname in
                                          let uu____1609 =
                                            FStar_Util.must
                                              ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc in
                                          FStar_Extraction_ML_UEnv.extend_fv'
                                            env uu____1608 mname uu____1609
                                            ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                            false in
                                        match uu____1605 with
                                        | (env1,uu____1613) ->
                                            (env1,
                                              (let uu___163_1614 = ml_lb in
                                               {
                                                 FStar_Extraction_ML_Syntax.mllb_name
                                                   =
                                                   ((Prims.snd mname),
                                                     (Prims.parse_int "0"));
                                                 FStar_Extraction_ML_Syntax.mllb_tysc
                                                   =
                                                   (uu___163_1614.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                 FStar_Extraction_ML_Syntax.mllb_add_unit
                                                   =
                                                   (uu___163_1614.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                 FStar_Extraction_ML_Syntax.mllb_def
                                                   =
                                                   (uu___163_1614.FStar_Extraction_ML_Syntax.mllb_def);
                                                 FStar_Extraction_ML_Syntax.print_typ
                                                   =
                                                   (uu___163_1614.FStar_Extraction_ML_Syntax.print_typ)
                                               }))
                                      else
                                        (let uu____1617 =
                                           let uu____1618 =
                                             let uu____1621 =
                                               FStar_Util.must
                                                 ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc in
                                             FStar_Extraction_ML_UEnv.extend_lb
                                               env lbname t uu____1621
                                               ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                               false in
                                           FStar_All.pipe_left Prims.fst
                                             uu____1618 in
                                         (uu____1617, ml_lb)) in
                                    (match uu____1591 with
                                     | (g1,ml_lb1) ->
                                         (g1, (ml_lb1 :: ml_lbs)))) (g, [])
                         bindings (Prims.snd lbs) in
                     (match uu____1543 with
                      | (g1,ml_lbs') ->
                          let flags =
                            FStar_List.choose
                              (fun uu___159_1641  ->
                                 match uu___159_1641 with
                                 | FStar_Syntax_Syntax.Assumption  ->
                                     Some FStar_Extraction_ML_Syntax.Assumed
                                 | FStar_Syntax_Syntax.Private  ->
                                     Some FStar_Extraction_ML_Syntax.Private
                                 | FStar_Syntax_Syntax.NoExtract  ->
                                     Some
                                       FStar_Extraction_ML_Syntax.NoExtract
                                 | uu____1643 -> None) quals in
                          let flags' =
                            FStar_List.choose
                              (fun uu___160_1648  ->
                                 match uu___160_1648 with
                                 | {
                                     FStar_Syntax_Syntax.n =
                                       FStar_Syntax_Syntax.Tm_constant
                                       (FStar_Const.Const_string
                                       (data,uu____1653));
                                     FStar_Syntax_Syntax.tk = uu____1654;
                                     FStar_Syntax_Syntax.pos = uu____1655;
                                     FStar_Syntax_Syntax.vars = uu____1656;_}
                                     ->
                                     Some
                                       (FStar_Extraction_ML_Syntax.Attribute
                                          (FStar_Util.string_of_unicode data))
                                 | uu____1661 ->
                                     (FStar_Util.print_warning
                                        "Warning: unrecognized, non-string attribute, bother protz for a better error message";
                                      None)) attrs in
                          let uu____1665 =
                            let uu____1667 =
                              let uu____1669 =
                                let uu____1670 =
                                  FStar_Extraction_ML_Util.mlloc_of_range
                                    se.FStar_Syntax_Syntax.sigrng in
                                FStar_Extraction_ML_Syntax.MLM_Loc uu____1670 in
                              [uu____1669;
                              FStar_Extraction_ML_Syntax.MLM_Let
                                (flavor, (FStar_List.append flags flags'),
                                  (FStar_List.rev ml_lbs'))] in
                            FStar_List.append uu____1667
                              tactic_registration_decl in
                          (g1, uu____1665))
                 | uu____1674 ->
                     let uu____1675 =
                       let uu____1676 =
                         FStar_Extraction_ML_Code.string_of_mlexpr
                           g.FStar_Extraction_ML_UEnv.currentModule ml_let in
                       FStar_Util.format1
                         "Impossible: Translated a let to a non-let: %s"
                         uu____1676 in
                     failwith uu____1675))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____1681,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____1685 =
             FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption) in
           if uu____1685
           then
             let always_fail =
               let imp =
                 let uu____1692 = FStar_Syntax_Util.arrow_formals t in
                 match uu____1692 with
                 | ([],t1) ->
                     let b =
                       let uu____1711 =
                         FStar_Syntax_Syntax.gen_bv "_" None t1 in
                       FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                         uu____1711 in
                     let uu____1712 = fail_exp lid t1 in
                     FStar_Syntax_Util.abs [b] uu____1712 None
                 | (bs,t1) ->
                     let uu____1730 = fail_exp lid t1 in
                     FStar_Syntax_Util.abs bs uu____1730 None in
               let uu___164_1736 = se in
               let uu____1737 =
                 let uu____1738 =
                   let uu____1744 =
                     let uu____1748 =
                       let uu____1750 =
                         let uu____1751 =
                           let uu____1754 =
                             FStar_Syntax_Syntax.lid_as_fv lid
                               FStar_Syntax_Syntax.Delta_constant None in
                           FStar_Util.Inr uu____1754 in
                         {
                           FStar_Syntax_Syntax.lbname = uu____1751;
                           FStar_Syntax_Syntax.lbunivs = [];
                           FStar_Syntax_Syntax.lbtyp = t;
                           FStar_Syntax_Syntax.lbeff =
                             FStar_Syntax_Const.effect_ML_lid;
                           FStar_Syntax_Syntax.lbdef = imp
                         } in
                       [uu____1750] in
                     (false, uu____1748) in
                   (uu____1744, [], []) in
                 FStar_Syntax_Syntax.Sig_let uu____1738 in
               {
                 FStar_Syntax_Syntax.sigel = uu____1737;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___164_1736.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___164_1736.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___164_1736.FStar_Syntax_Syntax.sigmeta)
               } in
             let uu____1761 = extract_sig g always_fail in
             (match uu____1761 with
              | (g1,mlm) ->
                  let uu____1772 =
                    FStar_Util.find_map quals
                      (fun uu___161_1774  ->
                         match uu___161_1774 with
                         | FStar_Syntax_Syntax.Discriminator l -> Some l
                         | uu____1777 -> None) in
                  (match uu____1772 with
                   | Some l ->
                       let uu____1782 =
                         let uu____1784 =
                           let uu____1785 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____1785 in
                         let uu____1786 =
                           let uu____1788 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l in
                           [uu____1788] in
                         uu____1784 :: uu____1786 in
                       (g1, uu____1782)
                   | uu____1790 ->
                       let uu____1792 =
                         FStar_Util.find_map quals
                           (fun uu___162_1794  ->
                              match uu___162_1794 with
                              | FStar_Syntax_Syntax.Projector (l,uu____1797)
                                  -> Some l
                              | uu____1798 -> None) in
                       (match uu____1792 with
                        | Some uu____1802 -> (g1, [])
                        | uu____1804 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____1810 = FStar_Extraction_ML_Term.term_as_mlexpr g e in
           (match uu____1810 with
            | (ml_main,uu____1818,uu____1819) ->
                let uu____1820 =
                  let uu____1822 =
                    let uu____1823 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____1823 in
                  [uu____1822; FStar_Extraction_ML_Syntax.MLM_Top ml_main] in
                (g, uu____1820))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____1825 ->
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
      let uu____1845 =
        FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____1845 Prims.fst
let extract:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Extraction_ML_UEnv.env* FStar_Extraction_ML_Syntax.mllib
        Prims.list)
  =
  fun g  ->
    fun m  ->
      FStar_Syntax_Syntax.reset_gensym ();
      (let uu____1873 = FStar_Options.debug_any () in
       if uu____1873
       then
         let uu____1874 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
         FStar_Util.print1 "Extracting module %s\n" uu____1874
       else ());
      (let uu____1876 = FStar_Options.restore_cmd_line_options true in
       let name =
         FStar_Extraction_ML_Syntax.mlpath_of_lident
           m.FStar_Syntax_Syntax.name in
       let g1 =
         let uu___165_1879 = g in
         {
           FStar_Extraction_ML_UEnv.tcenv =
             (uu___165_1879.FStar_Extraction_ML_UEnv.tcenv);
           FStar_Extraction_ML_UEnv.gamma =
             (uu___165_1879.FStar_Extraction_ML_UEnv.gamma);
           FStar_Extraction_ML_UEnv.tydefs =
             (uu___165_1879.FStar_Extraction_ML_UEnv.tydefs);
           FStar_Extraction_ML_UEnv.currentModule = name
         } in
       let uu____1880 =
         FStar_Util.fold_map extract_sig g1
           m.FStar_Syntax_Syntax.declarations in
       match uu____1880 with
       | (g2,sigs) ->
           let mlm = FStar_List.flatten sigs in
           let is_kremlin =
             let uu____1897 = FStar_Options.codegen () in
             match uu____1897 with
             | Some "Kremlin" -> true
             | uu____1899 -> false in
           let uu____1901 =
             (((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
                (is_kremlin ||
                   (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)))
               &&
               (FStar_Options.should_extract
                  (m.FStar_Syntax_Syntax.name).FStar_Ident.str) in
           if uu____1901
           then
             ((let uu____1906 =
                 FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
               FStar_Util.print1 "Extracted module %s\n" uu____1906);
              (g2,
                [FStar_Extraction_ML_Syntax.MLLib
                   [(name, (Some ([], mlm)),
                      (FStar_Extraction_ML_Syntax.MLLib []))]]))
           else (g2, []))